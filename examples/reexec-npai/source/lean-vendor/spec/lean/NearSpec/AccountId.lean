import NearSpec.Bytes

/-!
# NEAR account ids (near-account-id 2.0.0, as locked by nearcore 2.13.4)

* `validate` — `near-account-id-2.0.0/src/validation.rs` `validate`:
  length 2..=64, chars `[a-z0-9-_.]`, no leading/trailing/consecutive separator.
* account types — `account_id_ref.rs` `get_account_type`:
  `is_eth_implicit` (`0x` + 40 lowercase hex), `is_near_implicit`
  (64 lowercase hex), `is_near_deterministic` (`0s` + 40 lowercase hex),
  otherwise `NamedAccount`.
Account ids are handled as their UTF-8 bytes (valid ids are ASCII).
-/

namespace NearSpec.AccountId

def isAlnum (c : UInt8) : Bool := (97 ≤ c.toNat && c.toNat ≤ 122) || (48 ≤ c.toNat && c.toNat ≤ 57)
def isSep (c : UInt8) : Bool := c.toNat == 45 || c.toNat == 95 || c.toNat == 46
def isHex (c : UInt8) : Bool := (97 ≤ c.toNat && c.toNat ≤ 102) || (48 ≤ c.toNat && c.toNat ≤ 57)

/-- Mirrors the `last_char_is_separator` loop of `validate` (starts `true`). -/
def charsOk : Bool → Bytes → Bool
  | lastSep, [] => !lastSep
  | lastSep, c :: cs =>
    if isAlnum c then charsOk false cs
    else if isSep c then (!lastSep) && charsOk true cs
    else false

def valid (s : Bytes) : Bool := 2 ≤ s.length && s.length ≤ 64 && charsOk true s

def allHex (s : Bytes) : Bool := s.all isHex

def isNearImplicit (s : Bytes) : Bool := s.length == 64 && allHex s
def isEthImplicit (s : Bytes) : Bool :=
  s.length == 42 && s.take 2 == [48, 120] && allHex (s.drop 2)        -- "0x"
def isNearDeterministic (s : Bytes) : Bool :=
  s.length == 42 && s.take 2 == [48, 115] && allHex (s.drop 2)        -- "0s"

def isNamed (s : Bytes) : Bool :=
  !(isEthImplicit s || isNearImplicit s || isNearDeterministic s)

/-- `"system"` -/
def system : Bytes := [115, 121, 115, 116, 101, 109]

end NearSpec.AccountId
