
#include <stdio.h>
#include <stdlib.h>

#define SIZE 32768

char buf[SIZE];

int main(){

  FILE *f = fopen("f.txt","rb");
  fseek(f,0,SEEK_END);
  int s = ftell(f);
  rewind(f);

  for(int i=0; i<s; i+=SIZE){
    if(s-i <= SIZE)
      fread(buf,1,s-i,f);
    else
      fread(buf,1,SIZE,f);
  }
  fclose(f);
}
