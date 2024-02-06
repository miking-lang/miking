(module
    (func (export "mexpr") (result i32)
        (if (i32.eq (i32.const 1) (i32.const 1))
            (then (i32.const 10))
            (else (i32.const 20)))
    )
)