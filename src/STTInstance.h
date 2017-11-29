using namespace std;
#include <vector>
#include <string>
#include <cstdio>

struct InfoProfesores{
  int iden;
  int idenExterna;
  char *disponibilidad;
};


struct InfoPeriodos{
  int iden;
  int tipo;
  int dia;
};


struct InfoAulas{
  int iden;
  int capacidad;
  char *disponibilidad;
};


struct InfoCursos{
  int iden;
  int numEstudiantes;
  char *disponibilidad;
  char nombre[50];
};

struct InfoMaterias{
  int iden;
  int complejidad;
  char* disponibilidad;
  char nombre[50];
};


struct InfoReuniones{
  int idenReunion;
  int idenMateria;
  int idenProfesor;
  int idenAula;
  int idenCurso;
  int idenPeriodo;
  int numDepHor;
  int numDepVer;
  vector<int> depHor;
  vector<int> depVer;
};

struct STTInstance{
  int numPeriodos;
  int numCursos;
  int numAulas;
  int numMaterias;
  int numProfesores;
  int numDias;
  vector<InfoProfesores> datosProfesores;
  vector<InfoPeriodos> datosPeriodos;
  vector<InfoAulas> datosAulas;
  vector<InfoCursos> datosCursos;
  vector<InfoMaterias> datosMaterias;
  vector<InfoReuniones> datosReuniones;
  vector< vector<int> > reunionesPorCurso;
  vector< vector<int> > reunionesPorProfesor;
  vector< vector<int> > reunionesPorAula;

  STTInstance(char* fileName){
    int i,j,k;
    FILE* f=fopen(fileName,"rt");
    fscanf(f,"%d\n",&numCursos); //recuperar constantes generales
    fscanf(f,"%d\n",&numPeriodos);
    fscanf(f,"%d\n",&numMaterias);
    fscanf(f,"%d\n",&numProfesores);
    fscanf(f,"%d\n",&numAulas);
    fscanf(f,"%d\n",&numDias); 
    fscanf(f,"\n");

    /*Reservar memoria*/
    datosProfesores.resize(numProfesores+1);
    datosPeriodos.resize(numPeriodos+1);
    datosAulas.resize(numAulas+1);
    datosCursos.resize(numCursos+1);
    datosMaterias.resize(numMaterias+1);
    datosReuniones.resize(numCursos*numPeriodos);
    reunionesPorProfesor.resize(numProfesores);
    reunionesPorCurso.resize(numCursos);
    reunionesPorAula.resize(numAulas);
    
    for(i=0;i<numProfesores;i++){
      datosProfesores[i].disponibilidad=(char*)malloc((numPeriodos+1)*sizeof(char));
      reunionesPorProfesor[i] = vector<int>();
    }
    for(i=0;i<numAulas;i++){
      datosAulas[i].disponibilidad=(char*)malloc((numPeriodos+1)*sizeof(char));
      reunionesPorAula[i] = vector<int>();
    }
    for(i=0;i<numCursos;i++){
      datosCursos[i].disponibilidad=(char*)malloc((numPeriodos+1)*sizeof(char));
      reunionesPorCurso[i] = vector<int>();
    }
    for(i=0;i<numMaterias;i++){
      datosMaterias[i].disponibilidad=(char*)malloc((numPeriodos+1)*sizeof(char));
    }
    
    /*Leer datos*/
    for(i=0 ; i<numPeriodos ; i++){//periodos
      fscanf(f,"%d %d %d\n",&(datosPeriodos[i].iden), &(datosPeriodos[i].tipo), &(datosPeriodos[i].dia));
    }
    fscanf(f,"\n");

    int idReunion, idCurso,idMateria,idProfesor,idAula,numDepHor,numDepVer,dep;
    for(i=0;i<numCursos;i++){//meetings
      for(j=0;j<numPeriodos;j++){
	fscanf(f,"%d %d %d %d %d %d %d\n",&idReunion,&idCurso,&idMateria,&idProfesor,&idAula,&numDepHor,&numDepVer);
	idCurso--;
	idReunion--;
	datosReuniones[idReunion].idenReunion  = idReunion;
	datosReuniones[idReunion].idenCurso    = idCurso;
	datosReuniones[idReunion].idenMateria  = idMateria;
	datosReuniones[idReunion].idenProfesor = idProfesor;
	datosReuniones[idReunion].idenAula     = idAula;
      
	if(idProfesor) reunionesPorProfesor[idProfesor].push_back(idReunion);
	if(idAula) reunionesPorAula[idAula].push_back(idReunion);
	reunionesPorCurso[idCurso].push_back(idReunion);
	    
	for(k=0; k < numDepHor ;k++){
	  fscanf(f,"%d\n",&dep);
	  dep--;
	  datosReuniones[idReunion].depHor.push_back(dep);
	}
	for(k=0;k<numDepVer;k++){
	  fscanf(f,"%d\n",&dep);
	  dep--;
	  datosReuniones[idReunion].depVer.push_back(dep);
	}
      }
    }

    fscanf(f,"\n");
    for(i=0;i<numProfesores;i++){//Profesores
      fscanf(f,"%d %s\n",&datosProfesores[i].iden,datosProfesores[i].disponibilidad);
    }
  
    fscanf(f,"\n");
    for(i=0;i<numMaterias;i++){//Materias
      fscanf(f,"%s %s\n",datosMaterias[i].disponibilidad,datosMaterias[i].nombre);
    }

    fscanf(f,"\n");
    for(i=0;i<numCursos;i++){//Cursos
      fscanf(f,"%s %s\n",datosCursos[i].disponibilidad,datosCursos[i].nombre);
    }
    fclose(f);
  }

  void print(){
    for(int i=0;i<datosReuniones.size();++i){
      printf("(%d,%s,%s), ",datosReuniones[i].idenReunion, datosCursos[datosReuniones[i].idenCurso].nombre, datosMaterias[datosReuniones[i].idenMateria].nombre);
      if((i+1)%numPeriodos==0) printf("\n");
    }
  }
};
