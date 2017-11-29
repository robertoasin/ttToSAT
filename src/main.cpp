//#include "STTInstance.h"
#include "encoder.h"

int main(int argc, char**argv){
  STTInstance instance(argv[1]);
  //instance.print();
  TTEncoder enc;
  enc.encodeInstance(argv[2],instance);
  //  enc.prueba();
  int a,b;
  return(0);
}
