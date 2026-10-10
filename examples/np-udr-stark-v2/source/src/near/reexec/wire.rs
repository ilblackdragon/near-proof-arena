//! Strict little-endian (borsh-style) reader and writer.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireError(pub &'static str);

impl std::fmt::Display for WireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

pub type WResult<T> = Result<T, WireError>;

/// Cursor over a byte slice. Every read fails on truncation.
pub struct Reader<'a> {
    pub buf: &'a [u8],
    pub pos: usize,
}

impl<'a> Reader<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Reader { buf, pos: 0 }
    }
    #[inline]
    pub fn take(&mut self, n: usize, what: &'static str) -> WResult<&'a [u8]> {
        let end = self.pos.checked_add(n).ok_or(WireError(what))?;
        if end > self.buf.len() {
            return Err(WireError(what));
        }
        let s = &self.buf[self.pos..end];
        self.pos = end;
        Ok(s)
    }
    #[inline]
    pub fn u8(&mut self, what: &'static str) -> WResult<u8> {
        Ok(self.take(1, what)?[0])
    }
    #[inline]
    pub fn u16(&mut self, what: &'static str) -> WResult<u16> {
        Ok(u16::from_le_bytes(self.take(2, what)?.try_into().unwrap()))
    }
    #[inline]
    pub fn u32(&mut self, what: &'static str) -> WResult<u32> {
        Ok(u32::from_le_bytes(self.take(4, what)?.try_into().unwrap()))
    }
    #[inline]
    pub fn u64(&mut self, what: &'static str) -> WResult<u64> {
        Ok(u64::from_le_bytes(self.take(8, what)?.try_into().unwrap()))
    }
    #[inline]
    pub fn u128(&mut self, what: &'static str) -> WResult<u128> {
        Ok(u128::from_le_bytes(
            self.take(16, what)?.try_into().unwrap(),
        ))
    }
    #[inline]
    pub fn hash(&mut self, what: &'static str) -> WResult<[u8; 32]> {
        Ok(self.take(32, what)?.try_into().unwrap())
    }
    #[inline]
    pub fn bytes(&mut self, what: &'static str) -> WResult<&'a [u8]> {
        let n = self.u32(what)? as usize;
        self.take(n, what)
    }
    pub fn expect_tag(&mut self, want: &[u8], what: &'static str) -> WResult<()> {
        if self.bytes(what)? == want {
            Ok(())
        } else {
            Err(WireError(what))
        }
    }
    pub fn is_empty(&self) -> bool {
        self.pos == self.buf.len()
    }
    pub fn finish(&self) -> WResult<()> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(WireError("trailing bytes"))
        }
    }
}

/// Append-only writer.
#[derive(Default)]
pub struct Writer(pub Vec<u8>);

impl Writer {
    pub fn with_capacity(n: usize) -> Self {
        Writer(Vec::with_capacity(n))
    }
    #[inline]
    pub fn u8(&mut self, x: u8) -> &mut Self {
        self.0.push(x);
        self
    }
    #[inline]
    pub fn u16(&mut self, x: u16) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    #[inline]
    pub fn u32(&mut self, x: u32) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    #[inline]
    pub fn u64(&mut self, x: u64) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    #[inline]
    pub fn u128(&mut self, x: u128) -> &mut Self {
        self.0.extend_from_slice(&x.to_le_bytes());
        self
    }
    #[inline]
    pub fn raw(&mut self, b: &[u8]) -> &mut Self {
        self.0.extend_from_slice(b);
        self
    }
    #[inline]
    pub fn bytes(&mut self, b: &[u8]) -> &mut Self {
        self.u32(b.len() as u32).raw(b)
    }
}
