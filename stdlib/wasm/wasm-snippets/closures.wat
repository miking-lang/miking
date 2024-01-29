(module
    (table 2 funcref)
    (memory $memory 1000)
    (func $nullaryFunc (result i32) i32.const 42)
    (func $unaryFunc (param i32) (result i32) 
        local.get 0
        i32.const 1
        i32.add
    )
    (elem (i32.const 0) $nullaryFunc $unaryFunc)
    (type $nullary (func (result i32)))
    (type $unary (func (param i32) (result i32)))

    (func $call-closure (param $addr i32) (result i32)
        (local $result i32)
        (local.get $addr)
        (i32.load offset=0 align=4)
        (i32.const 0)
        (i32.eq)
        (if (then
            (local.get $addr)
            (i32.load offset=4 align=4)
            (call_indirect (type $nullary))
            (local.set $result)
        ) (else 
            ;; Push arg0 to stack
            (local.get $addr)
            (i32.load offset=8 align=4)
            ;; Push func_addr to stack
            (local.get $addr)
            (i32.load offset=4 align=4)
            (call_indirect (type $unary))
            (local.set $result)
        ))
        (local.get $result)
    )

    (func (export "main") (result i32)
        ;; Init [0..8) with call to nullaryFunc
        ;; Set arity=0
        (i32.const 0)
        (i32.const 0)
        (i32.store offset=0 align=4)
        ;; Set table_addr = 0
        (i32.const 0)
        (i32.const 0)
        (i32.store offset=4 align=4)

        ;; Init [5..14) with call to unaryFunc with param 22
        ;; Set arity = 1
        (i32.const 8)
        (i32.const 1)
        (i32.store offset=0 align=4)
        ;; Set table_addr = 1
        (i32.const 8)
        (i32.const 1)
        (i32.store offset=4 align=4)
        ;; Set arg0 = 22
        (i32.const 8)
        (i32.const 22)
        (i32.store offset=8 align=4)
        
        (i32.const 8)
        (call $call-closure)
    )
)