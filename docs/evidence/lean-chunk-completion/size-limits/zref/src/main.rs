// Reference zstd harness mirroring nearcore's CompressedData encode/decode.
use std::io::{Read, Write};

// nearcore CountingRead: errors (WriteZero) when total_read > hard_limit.
struct CountingRead<R> { inner: R, total: u64, limit: u64 }
impl<R: Read> Read for CountingRead<R> {
    fn read(&mut self, b: &mut [u8]) -> std::io::Result<usize> {
        let n = self.inner.read(b)?;
        self.total = self.total.saturating_add(n as u64);
        if self.total > self.limit {
            return Err(std::io::Error::new(std::io::ErrorKind::WriteZero, "limit"));
        }
        Ok(n)
    }
}

fn encode(input: &[u8], level: i32, workers: u32) -> Vec<u8> {
    let mut enc = zstd::stream::Encoder::new(Vec::new(), level).unwrap();
    enc.multithread(workers).unwrap();
    enc.write_all(input).unwrap();
    enc.finish().unwrap()
}

// Decode the whole frame reading to EOF under a byte limit, mirroring how
// borsh::from_reader(CountingRead(zstd::Decoder)) reads the full object.
fn decode_full(frame: &[u8], limit: u64) -> Result<Vec<u8>, String> {
    let dec = zstd::stream::Decoder::new(std::io::Cursor::new(frame)).map_err(|e| format!("new:{e}"))?;
    let mut cr = CountingRead { inner: dec, total: 0, limit };
    let mut out = Vec::new();
    match cr.read_to_end(&mut out) {
        Ok(_) => Ok(out),
        Err(e) => Err(format!("{:?}:{}", e.kind(), e)),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args[1].as_str() {
        // encode <in> <out> [level] [workers]
        "encode" => {
            let input = std::fs::read(&args[2]).unwrap();
            let level = args.get(4).map(|s| s.parse().unwrap()).unwrap_or(1);
            let workers = args.get(5).map(|s| s.parse().unwrap()).unwrap_or(4);
            std::fs::write(&args[3], encode(&input, level, workers)).unwrap();
        }
        // decode <frame> <out> <limit>  -> prints OK <len> or ERR <msg>
        "decode" => {
            let frame = std::fs::read(&args[2]).unwrap();
            let limit: u64 = args[4].parse().unwrap();
            match decode_full(&frame, limit) {
                Ok(o) => { std::fs::write(&args[3], &o).unwrap(); println!("OK {}", o.len()); }
                Err(e) => { println!("ERR {}", e); }
            }
        }
        _ => { eprintln!("usage"); std::process::exit(2); }
    }
}
