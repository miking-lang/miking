clear; 
wasm-as -all $1 -o $2; 
echo $1; 
echo $2;
while inotifywait -e close_write $1; do 
    clear; 
    wasm-as -all $1 -o $2; 
done
