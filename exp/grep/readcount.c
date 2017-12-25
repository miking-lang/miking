
#include <stdio.h>
#include <stdlib.h>

//#define DOPRINT

#define SIZE 32768

char buf[SIZE];

char c = ',';
int count = 0;

int main(){

  FILE *f = fopen("f.txt","rb");
  fseek(f,0,SEEK_END);
  int s = ftell(f);
  rewind(f);

  for(int i=0; i<s; i+=SIZE){
    int l = SIZE;
    if(s-i <= SIZE){
      l = s-i;
      fread(buf,1,l,f);
    }
    else
      fread(buf,1,SIZE,f);

    for(int j=0; j<l; j++){
      if(buf[j] == c)
        count++;
    }
  }
  fclose(f);
  #ifdef DOPRINT
    printf("count = %d\n", count);
  #endif
}
