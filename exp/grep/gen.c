

#include <stdio.h>


int main(){
  int lines = 1000000;
  int special = 10;
  
  for(int i=0; i<lines; i++){
    if(i % (lines/special) == 0)
      printf("This is the 12 special line ,the text,\n");
    else
      printf("Some normal text that might change in the future\n");
  }
}
