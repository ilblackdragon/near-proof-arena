// Copyright 2025-2026 The Binius Developers.
// Derived from binius64 81cdfff40cb21746581df0b5ea34eaf1761bc82f,
// crates/circuits/src/sha256/mod.rs (Apache-2.0).
// Local change: explicit tighter byte bound, enforced by len_check below,
// and derive block capacity from that bound rather than rounded storage words.
use binius_core::word::Word;
use binius_frontend::{CircuitBuilder,Wire};
use binius_circuits::{bytes::swap_bytes_32,fixed_byte_vec::ByteVec,
 multiplexer::{multi_wire_multiplex,single_wire_multiplex},util::clear_high_bits,
 sha256::{State,sha256_compress,sha256_compress_2x_seq}};
pub fn sha256_tight(builder: &CircuitBuilder, message: &ByteVec, max_len_bytes: usize) -> [Wire; 4] {
	// ---- 1. Input validation and setup
	//
	// Cap the maximum bit length so the 64-bit length field's low 32 bits suffice, compute the
	// number of compression blocks (accounting for the minimum 9 bytes of padding), and verify the
	// actual length is within bounds.
	let len_bytes = message.len_bytes;
	assert!(
		message.data.len() << Word::LOG_BITS <= u32::MAX as usize,
		"length of message in bits must fit within 32 bits"
	);

	assert!(max_len_bytes <= message.data.len() * 8);
	let n_blocks = (max_len_bytes + 9).div_ceil(64);
	let n_words: usize = n_blocks << 4; // 16 words per block

	let too_long = builder.icmp_ugt(len_bytes, builder.add_constant_64(max_len_bytes as u64));
	builder.assert_false("len_check", too_long);

	// `ByteVec` packs bytes little-endian; `sha256_compress` consumes big-endian 32-bit words. Each
	// 64-bit data word carries two schedule words: `swap_bytes_32` byte-reverses within each 32-bit
	// half, so the low half becomes the big-endian schedule word for the first four bytes and the
	// high half the schedule word for the next four. Split each into two low-32 wires.
	let mut message_be: Vec<Wire> = Vec::with_capacity(message.data.len() * 2);
	for &word in &message.data {
		let swapped = swap_bytes_32(builder, word);
		message_be.push(clear_high_bits(builder, swapped, 32));
		message_be.push(builder.shr(swapped, 32));
	}

	// ---- 2a. SHA-256 padding position calculation
	let zero = builder.add_constant(Word::ZERO);
	let w_bd = builder.shr(len_bytes, 2);
	let len_mod_4 = builder.band(len_bytes, builder.add_constant_zx_8(3));
	let bitlen = builder.shl(len_bytes, 3);

	// end_block_index = floor((len + 8) / 64) using a 64-bit add.
	let (sum, _carry) = builder.iadd(len_bytes, builder.add_constant_64(8));
	let end_block_index = builder.shr(sum, 6);

	// ---- Boundary word construction
	//
	// The 32-bit word at index `w_bd` mixes the trailing message bytes with the 0x80 delimiter.
	// Build the four candidate words (keeping `i` leading message bytes and placing the delimiter
	// at byte `i`) and select the one for `len_mod_4`. When `len_mod_4 == 0` the chosen candidate
	// is `0x80000000` independent of the (possibly out-of-range) boundary message word, so the
	// multiplexer's result is irrelevant in that case.
	let boundary_message_word = single_wire_multiplex(builder, &message_be, w_bd);
	let candidates: Vec<Wire> = (0..4)
		.map(|i| {
			let mask = builder.add_constant_64((0xFFFFFFFFu64 << ((4 - i) << 3)) & 0xFFFFFFFF);
			let padding_byte = builder.add_constant_64(0x80000000u64 >> (i << 3));
			let message_low = builder.band(boundary_message_word, mask);
			builder.bxor(message_low, padding_byte)
		})
		.collect();
	let boundary_word = single_wire_multiplex(builder, &candidates, len_mod_4);

	// ---- Padded message words
	//
	// Compute each 32-bit padded word as a derived wire, classifying its position:
	//
	//     1. word_index <  w_bd - pure message word
	//     2. word_index == w_bd - boundary word (message bytes + 0x80 delimiter)
	//     3. word_index >  w_bd - pure padding, except word 15 of the length block (the bit length)
	let padded_message: Vec<Wire> = (0..n_words)
		.map(|word_index| {
			let block_index = word_index >> 4;
			let column_index = word_index & 15;

			let is_message_word =
				builder.icmp_ult(builder.add_constant_64(word_index as u64), w_bd);
			let is_boundary_word =
				builder.icmp_eq(builder.add_constant_64(word_index as u64), w_bd);
			let is_length_block =
				builder.icmp_eq(builder.add_constant_64(block_index as u64), end_block_index);

			// Pure message words select the corresponding schedule word. This is only ever selected
			// when word_index < w_bd ≤ max_len_bytes >> 2 == message_be.len(), so the index is in
			// range; the zero fallback for word_index ≥ message_be.len() is never chosen.
			let msg_word = if word_index < message_be.len() {
				message_be[word_index]
			} else {
				zero
			};

			// Padding words are zero, except word 15 of the length block which holds the bit
			// length. (Word 14 — the high 32 bits of the 64-bit length — stays zero, since only
			// ≤ 32-bit bit lengths are supported.)
			let past_word = if column_index == 15 {
				builder.select(is_length_block, bitlen, zero)
			} else {
				zero
			};

			let boundary_or_past = builder.select(is_boundary_word, boundary_word, past_word);
			builder.select(is_message_word, msg_word, boundary_or_past)
		})
		.collect();

	// ---- Compression chain
	//
	// Compress two chained blocks per step through one parallel core: `sha256_compress_2x_seq` runs
	// both in the two 32-bit lanes of a 64-bit word, for ~the AND cost of a single compression. The
	// paired output packs the state after the first block in the high 32 bits and the state after
	// the second block in the low 32 bits. `states[k]` therefore ends up being the state after
	// block `k - 1`, exactly as a single-lane chain would produce, so the digest multiplexer is
	// unchanged.
	let mut states = Vec::with_capacity(n_blocks + 1);
	states.push(State::iv(builder));
	let mk_m = |block_no: usize| -> [Wire; 16] {
		padded_message[block_no << 4..(block_no + 1) << 4]
			.try_into()
			.unwrap()
	};
	let mut block_no = 0;
	while block_no + 1 < n_blocks {
		let out = sha256_compress_2x_seq(
			&builder.subcircuit(format!("compress[{block_no}..{}]", block_no + 2)),
			states[block_no],
			[mk_m(block_no), mk_m(block_no + 1)],
		);
		// Clearing the high half restores the empty half that the single-lane digest packing
		// relies on.
		let state_first = State::new(std::array::from_fn(|i| builder.shr(out.0[i], 32)));
		let state_second =
			State::new(std::array::from_fn(|i| clear_high_bits(builder, out.0[i], 32)));
		states.push(state_first);
		states.push(state_second);
		block_no += 2;
	}
	// A trailing odd block has no partner, so compress it single-lane.
	if block_no < n_blocks {
		let state_out = sha256_compress(
			&builder.subcircuit(format!("compress[{block_no}]")),
			states[block_no],
			mk_m(block_no),
		);
		states.push(state_out);
	}

	// ---- Final digest selection
	//
	// The digest is the state after processing the block containing the length field, packed into
	// four 64-bit big-endian words. No caller-supplied digest is asserted — the packed selected
	// state IS the return value.
	let block_digests: Vec<[Wire; 4]> = states[1..].iter().map(|s| s.pack_4x64b(builder)).collect();
	let inputs: Vec<&[Wire]> = block_digests.iter().map(|d| &d[..]).collect();
	let final_digest_vec = multi_wire_multiplex(builder, &inputs, end_block_index);
	final_digest_vec.try_into().unwrap()
}
