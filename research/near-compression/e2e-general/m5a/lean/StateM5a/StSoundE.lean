import StateM5a.St
import NearSpec.SHA256

/-!
# StateM5a.StSoundE — `SHA256_EMPTY` is `sha256 []`

`STW` fixes an empty value's digest to the constant `SHA256_EMPTY` (`St.lean`); this is the
specified `sha256` of the empty message (kernel evaluation of FIPS 180-4 on one padding block;
no `native_decide`).
-/

namespace StateM5a.StSound

theorem sha256_empty : NearSpec.sha256 [] = SHA256_EMPTY.map UInt8.ofNat := by decide +kernel

end StateM5a.StSound
