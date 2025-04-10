use {
    crate::{Arbitrary, MaxRecursionReached, Result, SizeHint, Unstructured},
    std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
};

impl<'a> Arbitrary<'a> for Ipv4Addr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Ipv4Addr::from(u32::arbitrary(u)?))
    }

    #[inline]
    fn size_hint(_depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(SizeHint::exactly(4))
    }
}

impl<'a> Arbitrary<'a> for Ipv6Addr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Ipv6Addr::from(u128::arbitrary(u)?))
    }

    #[inline]
    fn size_hint(_depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(SizeHint::exactly(16))
    }
}

impl<'a> Arbitrary<'a> for IpAddr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.arbitrary()? {
            Ok(IpAddr::V4(u.arbitrary()?))
        } else {
            Ok(IpAddr::V6(u.arbitrary()?))
        }
    }

    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(bool::size_hint(depth)? + (Ipv4Addr::size_hint(depth)? | Ipv6Addr::size_hint(depth)?))
    }
}

impl<'a> Arbitrary<'a> for SocketAddrV4 {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(SocketAddrV4::new(u.arbitrary()?, u.arbitrary()?))
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(Ipv4Addr::size_hint(depth)? + u16::size_hint(depth)?)
    }
}

impl<'a> Arbitrary<'a> for SocketAddrV6 {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(SocketAddrV6::new(
            u.arbitrary()?,
            u.arbitrary()?,
            u.arbitrary()?,
            u.arbitrary()?,
        ))
    }

    #[inline]
    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(Ipv6Addr::size_hint(depth)?
            + u16::size_hint(depth)?
            + u32::size_hint(depth)?
            + u32::size_hint(depth)?)
    }
}

impl<'a> Arbitrary<'a> for SocketAddr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        if u.arbitrary()? {
            Ok(SocketAddr::V4(u.arbitrary()?))
        } else {
            Ok(SocketAddr::V6(u.arbitrary()?))
        }
    }

    fn size_hint(depth: usize) -> Result<SizeHint, MaxRecursionReached> {
        Ok(bool::size_hint(depth)?
            + (SocketAddrV4::size_hint(depth)? | SocketAddrV6::size_hint(depth)?))
    }
}
