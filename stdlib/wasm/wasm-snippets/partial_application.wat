(module
    (memory 1000)
    (table 10 funcref)

    ;; Pointer to the first free memory address in the memory.
    (global $free_pointer (mut i32) (i32.const 0))

    (type $nullary (func (result i32)))
    (type $unary (func (param i32) (result i32)))
    (type $binary (func (param i32) (param i32) (result i32)))

    (func $addi (param i32) (param i32) (result i32)
        local.get 0
        local.get 1
        i32.add)

    (func $alloc-closure (param $func_pointer i32) (param $arity i32) (result i32)
        ;; Set current arity
        global.get $free_pointer
        i32.const 0
        i32.store offset=0 align=4

        ;; Set max arity
        global.get $free_pointer
        local.get $arity
        i32.store offset=4 align=4

        ;; Set function pointer
        global.get $free_pointer
        local.get $func_pointer
        i32.store offset=8 align=4
        
        global.get $free_pointer

        local.get $arity
        i32.const 3
        i32.add
        i32.const 4
        i32.mul
        global.get $free_pointer
        i32.add
        global.set $free_pointer)

    (func $apply (param $closure_pointer i32) (param $arg i32) (result i32)
        (local $cur_arity i32)
        (local $max_arity i32)
        (local $function_pointer i32)
        (local $result i32)
        (local $size i32)
        (local $i i32)

        local.get $closure_pointer
        i32.load offset=0 align=4
        local.set $cur_arity

        local.get $closure_pointer
        i32.load offset=4 align=4
        local.set $max_arity

        local.get $closure_pointer
        i32.load offset=8 align=4
        local.set $function_pointer

        ;; Compute size of new closure
        ;; size = (3 + max_arity) * 4
        i32.const 3
        local.get $max_arity
        i32.add
        i32.const 4
        i32.mul
        local.set $size

        ;; Copy old closure to new closure
        global.get $free_pointer ;; destination
        local.get $closure_pointer ;; source
        local.get $size ;; size
        memory.copy

        ;; Overwrite n_args
        global.get $free_pointer
        local.get $cur_arity
        i32.const 1
        i32.add
        i32.store offset=0 align=4

        ;; Overwrite correct arg
        i32.const 3
        local.get $cur_arity
        i32.add 
        i32.const 4
        i32.mul
        global.get $free_pointer
        i32.add
        local.get $arg
        i32.store offset=0 align=4

        ;; Update result
        global.get $free_pointer
        local.set $result

        ;; Update free pointer
        global.get $free_pointer
        local.get $size
        i32.add
        global.set $free_pointer

        local.get $result)

    (func $exec (param $closure_pointer i32) (result i32)
        local.get $closure_pointer
        i32.load offset=12 align=4

        local.get $closure_pointer
        i32.load offset=16 align=4

        local.get $closure_pointer
        i32.load offset=8 align=4

        call_indirect (type $binary))

    (elem (i32.const 0) $addi)

    (func (export "main") (result i32)
        ;; Test execution of expression (addi 3) 4
        i32.const 0 ;; func_pointer
        i32.const 2 ;; arity
        call $alloc-closure

        i32.const 23
        call $apply

        i32.const 42
        call $apply

        call $exec)

)