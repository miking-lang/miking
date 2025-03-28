
include "../string.mc"
include "../sys.mc"

-- Returns the number of CUDA devices available on the system. Uses nvcc to
-- retrieve the device count, so will also fail if nvcc is not present on the
-- system.
let cudaGetDeviceCount : () -> Option Int = lam.
    if not (sysCommandExists "nvcc") then
        None ()
    else -- continue
    sysWithTempDir (lam td.
      let checkProgPath = sysJoinPath td "check.cu" in
      let contents = "
#include <iostream>
int main()
{
    int c = 0;
    cudaError_t r = cudaGetDeviceCount(&c);
    if (r != cudaSuccess) {
       std::cout << cudaGetErrorString(r) << std::endl;
       return -1;
    } else {
       std::cout << c << std::endl;
       return 0;
    }
}
      " in
      writeFile checkProgPath contents;
      let run = lam cmd. sysRunCommand cmd "" td in

      match run ["nvcc", "check.cu", "--output-file", "check.out"]
      with execResult in
      if neqi execResult.returncode 0 then
        -- Assuming return code 0 indicated successful compilation here...
        None ()
      else -- continue

      match run ["./check.out"]
      with execResult in
      if eqi execResult.returncode 0 then
        -- The return code should be 0 if we could retrieve the CUDA device
        Some (string2int (strTrim execResult.stdout))
      else
        -- Something went wrong
        None ()
    )
