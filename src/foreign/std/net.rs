use {
    crate::{size_hint, Arbitrary, Result, SizeHint, Unstructured},
    std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6},
};

impl<'a> Arbitrary<'a> for Ipv4Addr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Ipv4Addr::from(u32::arbitrary(u)?))
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        SizeHint::exactly(4)
    }
}

impl<'a> Arbitrary<'a> for Ipv6Addr {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(Ipv6Addr::from(u128::arbitrary(u)?))
    }

    #[inline]
    fn size_hint(_context: &size_hint::Context) -> size_hint::SizeHint {
        SizeHint::exactly(16)
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

    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        context.get::<bool>() + (context.get::<Ipv4Addr>() | context.get::<Ipv6Addr>())
    }
}

impl<'a> Arbitrary<'a> for SocketAddrV4 {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        Ok(SocketAddrV4::new(u.arbitrary()?, u.arbitrary()?))
    }

    #[inline]
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        context.get::<Ipv4Addr>() + context.get::<u16>()
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
    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        context.get::<Ipv6Addr>()
            + context.get::<u16>()
            + context.get::<u32>()
            + context.get::<u32>()
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

    fn size_hint(context: &size_hint::Context) -> size_hint::SizeHint {
        context.get::<bool>() + (context.get::<SocketAddrV4>() | context.get::<SocketAddrV6>())
    }
}
