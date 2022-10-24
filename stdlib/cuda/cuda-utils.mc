-- defines the code for the cuda-utils.cuh file

let cudaUtilsCode = "
#include <stdlib.h>
#include <stdio.h>

void cuda_utils_checkCudaErr(const char *file, int line)
{
    cudaError_t err = cudaGetLastError();
    if (err != cudaSuccess) {
        fprintf(stderr, \"\\n%s:%d: received cuda error: %s\\n\", file, line, cudaGetErrorString(err));
        exit(1);
    }
}

#define CUDA_UTILS_CHECK_CUDA_ERROR() \\
        cuda_utils_checkCudaErr(__FILE__, __LINE__)

void cuda_utils_copyOCamlToCuda32Int(void *ocaml, void *cuda, int64_t size) {
  for (int64_t i = 0; i < size / sizeof(int64_t); i++) {
    ((int32_t*)cuda)[i] = (int32_t)(((int64_t*)ocaml)[i]);
  }
}

void cuda_utils_copyOCamlToCuda32Float(void *ocaml, void *cuda, int64_t size) {
  for (int64_t i = 0; i < size / sizeof(int64_t); i++) {
    ((float*)cuda)[i] = (float)(((double*)ocaml)[i]);
  }
}

void cuda_utils_copyOCamlToCuda64(void *ocaml, void *cuda, int64_t size) {
  cudaMemcpy(cuda, ocaml, size, cudaMemcpyHostToDevice);
  CUDA_UTILS_CHECK_CUDA_ERROR();
}

void cuda_utils_copyOCamlToCuda(void *ocaml, void *cuda, int64_t size, int64_t element_type) {
  if (element_type == 0) cuda_utils_copyOCamlToCuda64(ocaml, cuda, size);
  else if (element_type == 1) cuda_utils_copyOCamlToCuda32Int(ocaml, cuda, size);
  else cuda_utils_copyOCamlToCuda32Float(ocaml, cuda, size);
}

void cuda_utils_copyCuda32IntToOCaml(void *cuda, void *ocaml, int64_t size) {
  for (int64_t i = 0; i < size / sizeof(int64_t); i++) {
    ((int64_t*)ocaml)[i] = (int64_t)(((int32_t*)cuda)[i]);
  }
}

void cuda_utils_copyCuda32FloatToOCaml(void *cuda, void *ocaml, int64_t size) {
  for (int64_t i = 0; i < size / sizeof(int64_t); i++) {
    ((double*)ocaml)[i] = (double)(((float*)cuda)[i]);
  }
}

void cuda_utils_copyCuda64ToOCaml(void *cuda, void *ocaml, int64_t size) {
  cudaMemcpy(ocaml, cuda, size, cudaMemcpyDeviceToHost);
  CUDA_UTILS_CHECK_CUDA_ERROR();
}

void cuda_utils_copyCudaToOCaml(void *cuda, void *ocaml, int64_t size, int64_t element_type) {
  if (element_type == 0) cuda_utils_copyCuda64ToOCaml(cuda, ocaml, size);
  else if (element_type == 1) cuda_utils_copyCuda32IntToOCaml(cuda, ocaml, size);
  else cuda_utils_copyCuda32FloatToOCaml(cuda, ocaml, size);
}
"
