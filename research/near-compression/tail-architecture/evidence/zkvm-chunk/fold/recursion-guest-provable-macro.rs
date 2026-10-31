macro_rules! provable_with_config {
    ($item: item) => {
        #[jolt::provable(
            max_input_size = 134217728,
            max_output_size = 4096,
            max_untrusted_advice_size = 0,
            max_trusted_advice_size = 0,
            heap_size = 134217728,
            stack_size = 33554432,
            max_trace_length = 4000000000
        )]
        $item
    };
}