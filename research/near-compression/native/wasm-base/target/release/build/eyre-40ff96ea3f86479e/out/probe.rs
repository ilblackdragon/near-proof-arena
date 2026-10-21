
    #![feature(error_generic_member_access)]
    #![allow(dead_code)]

    use std::error::{Error, Request};
    use std::fmt::{self, Display};

    #[derive(Debug)]
    struct E { 
        backtrace: MyBacktrace,
    }

    #[derive(Debug)]
    struct MyBacktrace;

    impl Display for E {
        fn fmt(&self, _formatter: &mut fmt::Formatter) -> fmt::Result {
            unimplemented!()
        }
    }

    impl Error for E {
        fn provide<'a>(&'a self, request: &mut Request<'a>) {
            request
                .provide_ref::<MyBacktrace>(&self.backtrace);
        }
    }
