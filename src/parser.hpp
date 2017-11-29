#include "STTInstance.h"

STTInstance parse(char* archivoDatos){
  int i,j;
  FILE* f;
  f=fopen(archivoDatos,"rt");

  int numCursos, numPeriodos, numMaterias, numProfesores, numAulas, numDias;
  fscanf(f,"%d\n",&numCursos); //recuperar constantes generales
  fscanf(f,"%d\n",&numPeriodos);
  fscanf(f,"%d\n",&numMaterias);
  fscanf(f,"%d\n",&numProfesores);
  fscanf(f,"%d\n",&numAulas);
  fscanf(f,"%d\n",&numDias); 
  fscanf(f,"\n");

  STTInstance ttBenchmark(numCursos,numPeriodos,numMaterias,numProfesores,numAulas,numDias);

  for(i=0;i<ttBenchmark.numPeriodos;i++){//periodos
    fscanf(f,"%d %d %d\n",&(ttBenchmark.datosPeriodos[i].iden), &(ttBenchmark.datosPeriodos[i].tipo), &(ttBenchmark.datosPeriodos[i].dia));
  }

  fscanf(f,"\n");

  int idReunion, idCurso,idMateria,idProfesor,idAula,numDepHor,numDepVer,dep;
  for(i=0;i<ttBenchmark.numCursos;i++){//meetings
    for(j=0;j<ttBenchmark.numPeriodos;j++){
      fscanf(f,"%d %d %d %d %d %d %d\n",&idReunion,&idCurso,&idMateria,&idProfesor,&idAula,&numDepHor,&numDepVer);
      idCurso--;
      idReunion--;
      ttBenchmark.reuniones[idReunion].idenReunion  = idReunion;
      ttBenchmark.reuniones[idReunion].idenCurso    = idCurso;
      ttBenchmark.reuniones[idReunion].idenMateria  = idMateria;
      ttBenchmark.reuniones[idReunion].idenProfesor = idProfesor;
      ttBenchmark.reuniones[idReunion].idenAula     = idAula;
      
      if(idProfesor) ttBenchmark.reunionesPorProfesor[idProfesor].push_back(idReunion);
      if(idAula) ttBenchmark.reunionesPorAula[idAula].push_back(idReunion);
      ttBenchmark.reunionesPorAula[idCurso].push_back(idReunion);
	    
      for(k=0; k < numDepHor ;k++){
	fscanf(f,"%d\n",&dep);
	dep--;
	ttBenchmark.reuniones[idReunion].push_back(dep);
      }
      for(k=0;k<numDepVer;k++){
	fscanf(f,"%d\n",&dep);
	dep--;
	ttBenchmark.reuniones[idReunion].push_back(dep);
      }
    }
  }

  fscanf(f,"\n");
  for(i=0;i<ttBenchmark.numProfesores;i++){//Profesores
    fscanf(f,"%d %s\n",&ttBenchmark.datosProfesores[i].idenLocal,ttBenchmark.datosProfesores[i].disponibilidad);
  }
  
  fscanf(f,"\n");
  for(i=0;i<ttBenchmark.numMaterias;i++){//Materias
    fscanf(f,"%s %s\n",ttBenchmark.datosMaterias[i].disponibilidad,ttBenchmark.datosMaterias[i].nombre);
  }

  fscanf(f,"\n");
  for(i=0;i<ttBenchmark.numCursos;i++){//Cursos
    fscanf(f,"%s %s\n",ttBenchmark.datosCursos[i].disponibilidad,ttBenchmark.datosCursos[i].nombre);
  }
  fclose(f);
  /*Determinar reuniones Dependientes*/
  // for(i=0;i<ttBenchmark.numCursos;i++){
  //   for(j=0;j<ttBenchmark.numPeriodos;j++){
  //     if(ttBenchmark.reuniones[i][j].numDepHor>0){
  // 	for(l=0;l<ttBenchmark.reuniones[i][j].numDepHor;l++){
  // 	  for(k=0;k<ttBenchmark.numPeriodos;k++){
  // 	    if(ttBenchmark.reuniones[i][k].idenReunion==ttBenchmark.reuniones[i][j].depHor[l]){
  // 	      ttBenchmark.reuniones[i][j].dependenciasHorizontales[l]=k;
  // 	    }
  // 	  }
  // 	}
  //     }
  //   }
  // }
  return(ttBenchmark);
}
