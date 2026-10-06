from probe import *
def mod(bodies, extra_types=(), imports=(("env","value_return",[I64,I64],[]),)):
    """bodies: list of raw body bytes (locals vec + code, without size prefix)."""
    out = b"\x00asm\x01\x00\x00\x00"
    types = [functype([I64,I64],[]), functype([],[])]
    out += section(1, vec(types))
    out += section(2, vec([name(m)+name(n)+b"\x00"+uleb(0) for m,n,_,_ in imports]))
    out += section(3, vec([uleb(1)]*len(bodies)))
    out += section(7, vec([name("main")+b"\x00"+uleb(len(imports))]))
    out += section(10, vec([uleb(len(b))+b for b in bodies]))
    return out.hex()
ok = b"\x00\x0b"
bad = b"\x00\xff\x0b"
cases = [
 ("A bad-op body1, too-large body2", mod([bad, b"\x00" + b"\x01"*196608 + b"\x0b"])),
 ("B bad-op body1, too-many-locals body2", mod([bad, b"\x01\x81\xa4\x7a\x7f\x0b"])),  # 2,000,001 locals
 ("C 2,000,001 locals in one body", mod([b"\x01\x81\xa4\x7a\x7f\x0b"])),
 ("D 60000 locals", mod([b"\x01\xe0\xd4\x03\x7f\x0b"])),
 ("E (1000001,i32),(1,0x40)", mod([b"\x02\xc1\x84\x3d\x7f\x01\x40\x0b"])),
 ("F (1,0x40),(2000001,i32)", mod([b"\x02\x01\x40\x81\xa4\x7a\x7f\x0b"])),
 ("G (1, 0x81 0x01)", mod([b"\x01\x01\x81\x01\x0b"])),
 ("H (1,0x81 0x01),(2000001,i32)", mod([b"\x02\x01\x81\x01\x81\xa4\x7a\x7f\x0b"])),
 ("I (1,0x6f externref),(2000001,i32)", mod([b"\x02\x01\x6f\x81\xa4\x7a\x7f\x0b"])),
 ("J (1,0x7b v128),(2000001,i32)", mod([b"\x02\x01\x7b\x81\xa4\x7a\x7f\x0b"])),
 ("K (1,0x63 0x70),(2000001,i32)", mod([b"\x02\x01\x63\x70\x81\xa4\x7a\x7f\x0b"])),
 ("L (1,0x00),(2000001,i32)", mod([b"\x02\x01\x00\x81\xa4\x7a\x7f\x0b"])),
 ("M (40000,i32),(40000,i32) one body", mod([b"\x02\xc0\xb8\x02\x7f\xc0\xb8\x02\x7f\x0b"])),
 ("N bad-op body1, body2 locals ok", mod([bad, ok])),
 ("O bodysize > section", "00"),
]
cmp([(l, f"300000000000000 {h}") for l, h in cases])
