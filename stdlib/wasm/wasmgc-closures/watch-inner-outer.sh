clear; wasm-as -all inner-outer.wat -o inner-outer.wasm; 
while inotifywait -e close_write inner-outer.wat; 
    do clear; wasm-as -all inner-outer.wat -o inner-outer.wasm; 
done
