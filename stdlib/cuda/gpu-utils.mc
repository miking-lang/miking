-- defines the code for the gpu-utils.cu file

let gpu_utils_code = "
#include <stdlib.h>
#include <stdio.h>

void gpu_utils_checkCudaErr(const char *file, int line)
{
    cudaError_t err = cudaGetLastError();
    if (err != cudaSuccess) {
        fprintf(stderr, \"\\n%s:%d: received cuda error: %s\\n\", file, line, cudaGetErrorString(err));
        exit(1);
    }
}

#define GPU_UTILS_CHECK_CUDA_ERROR() \\
        gpu_utils_checkCudaErr(__FILE__, __LINE__)
"
