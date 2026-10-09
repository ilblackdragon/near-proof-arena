import ZkFormal.NearV3.Public.Bytes

/-! Compact prepared-statement segment metadata. All positions are byte offsets. -/
namespace ZkFormal.NearV3.Public

abbrev ByteString := List UInt8
abbrev Payload := List ByteString

def payloadBytes (rs : Payload) : ByteString := rs.flatten

def dataBytes (blocks : List Payload) : ByteString := blocks.flatMap payloadBytes

/-- Eight bytes per segment: u32 row count and u32 absolute payload offset. -/
def metadata : Nat → List Payload → ByteString
  | _, [] => []
  | start, rs :: rest => NearSpec.u32 rs.length ++ NearSpec.u32 start ++
      metadata (start + (payloadBytes rs).length) rest

def payloadOffset (start : Nat) (blocks : List Payload) (i : Nat) : Nat :=
  start + (dataBytes (blocks.take i)).length

def encode (header : ByteString) (blocks : List Payload) : ByteString :=
  header ++ metadata (header.length + 8 * blocks.length) blocks ++ dataBytes blocks

theorem metadata_length (start : Nat) (blocks : List Payload) :
    (metadata start blocks).length = 8 * blocks.length := by
  induction blocks generalizing start with
  | nil => rfl
  | cons rs rest ih => simp [metadata,NearSpec.u32,NearSpec.leN_length,ih]; omega

theorem getD_middle (pre mid post : ByteString) {i : Nat} (hi : i < mid.length) :
    (pre ++ mid ++ post).getD (pre.length+i) 0 = mid.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD,List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]

theorem getD_right (pre post : ByteString) (i : Nat) :
    (pre ++ post).getD (pre.length+i) 0 = post.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

theorem metadata_count (start : Nat) (blocks : List Payload) {i k : Nat}
    (hi : i < blocks.length) (hk : k < 4) :
    (metadata start blocks).getD (8*i+k) 0 =
      (NearSpec.u32 (blocks.getD i []).length).getD k 0 := by
  induction blocks generalizing start i with
  | nil => simp at hi
  | cons rs rest ih =>
    cases i with
    | zero =>
      simp only [metadata,Nat.mul_zero,Nat.zero_add,List.getD_cons_zero]
      rw [List.append_assoc]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa [NearSpec.u32,NearSpec.leN_length] using hk)]
    | succ i =>
      have hlen : (NearSpec.u32 rs.length ++ NearSpec.u32 start).length = 8 := by
        simp [NearSpec.u32,NearSpec.leN_length]
      simp only [metadata,List.getD_cons_succ]
      rw [show 8*(i+1)+k = (NearSpec.u32 rs.length ++ NearSpec.u32 start).length + (8*i+k) by omega,
        getD_right]
      exact ih _ (by simpa using hi)

theorem metadata_offset (start : Nat) (blocks : List Payload) {i k : Nat}
    (hi : i < blocks.length) (hk : k < 4) :
    (metadata start blocks).getD (8*i+4+k) 0 =
      (NearSpec.u32 (payloadOffset start blocks i)).getD k 0 := by
  induction blocks generalizing start i with
  | nil => simp at hi
  | cons rs rest ih =>
    cases i with
    | zero =>
      simp only [metadata,Nat.mul_zero,Nat.zero_add]
      rw [show 4+k = (NearSpec.u32 rs.length).length+k by simp [NearSpec.u32,NearSpec.leN_length],
        getD_middle _ _ _ (by simpa [NearSpec.u32,NearSpec.leN_length] using hk)]
      rfl
    | succ i =>
      have hlen : (NearSpec.u32 rs.length ++ NearSpec.u32 start).length = 8 := by
        simp [NearSpec.u32,NearSpec.leN_length]
      simp only [metadata]
      rw [show 8*(i+1)+4+k = (NearSpec.u32 rs.length ++ NearSpec.u32 start).length + (8*i+4+k) by omega,
        getD_right,ih _ (by simpa using hi)]
      congr 2
      simp [payloadOffset,dataBytes,Nat.add_assoc]

end ZkFormal.NearV3.Public
