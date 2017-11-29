#include "STTInstance.h"
#include <map>
#include <string>
#include "../pblib/pb2cnf.h"

struct TTEncoder{
  int numVars;
  int numClauses;
  map<string,int> varToInt;
  map<int,string> intToVar;
  
  TTEncoder(){
    numVars    = 0;
    numClauses = 0;
  }

  vector<string> split(const char *str, char c = ' ')
  {
    vector<string> result;

    do{
      const char *begin = str;

      while(*str != c && *str) str++;

      result.push_back(string(begin, str));
    } while (0 != *str++);

    return result;
  }
  
  void getMeetingAndTimeFromVar(string var, int &idReunion, int &idPeriodo){
    vector<string> parts = split(var.c_str(),'_');
    idReunion = stoi(parts[1]);
    idPeriodo = stoi(parts[2]);
  }
  
  string getMeetingTimeVar(int idReunion, int idPeriodo){
    return("x_"+to_string(idReunion)+'_'+to_string(idPeriodo));
  }
  
  void loadVarsFromInstance(STTInstance& ttInstance){
    //vars x_i_j -> reunion i ocurre en el periodo j
    for(int i=0;i<ttInstance.datosReuniones.size();++i){
      for(int j=0;j<ttInstance.numPeriodos;++j){
	varToInt[getMeetingTimeVar(i,j)]=numVars+1;
	intToVar[numVars+1]=getMeetingTimeVar(i,j);
	numVars++;
      }
    }
  }

  void encodeInstance(char* cnfFile, STTInstance& ttInstance){
    FILE *f = fopen(cnfFile,"wt");
    
    fclose(f);
  }
  
  void decodeInstance(char* modelFile, STTInstance& ttInstance){
    FILE *f = fopen(modelFile,"rt");
    
    fclose(f);
  }

  void prueba(){
    PB2CNF pb2cnf;
    vector< int32_t > literals = {-1,-2,3,4,5,-6, 10, -12, 14, -43, 44, 32, -28, -22, 9, 7, 33};
    vector< vector< int32_t > > formula;
    int32_t firstFreshVariable = 45;
    int k = 3;
    firstFreshVariable = pb2cnf.encodeAtMostK(literals, k, formula, firstFreshVariable) + 1;
    for(int i=0;i<formula.size();++i){
      for(int j=0;j<formula[i].size();++j){
	printf("%d ",formula[i][j]);
      }
      printf("\n");
    }
  }
};
