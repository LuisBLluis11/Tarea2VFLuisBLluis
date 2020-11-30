# Tarea2VFLuisBLluis
## Autor: Luis Felipe Benítez Lluis LL11
Repositorio con los archivos de coq correspondientes a la tarea 2 del curso de Verificación Formal 2021-1
## Arquitectura
Este repositorio cuenta con un archivo *_CoqProject* que maneja las
dependencias de los distintos archivos. EL proyecto contiene las siguientes carpetas:


1.   **LogicaMinimal** : esta carpeta contiene el archivo de coq *Prop_LM.v* donde se plantean los ejercicios de la sección 1 de así como los archivos correspondientes *.vo , .vok, .vos .glob, .aux*. No se precisó de tácticas ni definiciones.
2.   **LogicaIntuicionista**: esta carpeta contiene el archivo de coq *Prop_LI.v* donde se plantean los ejercicios de la sección 2 así como los archivos correspondientes *.vo , .vok, .vos .glob, .aux*. No se precisó de tácticas ni definiciones.
3.   **LogicaClasica** : esta carpeta contiene los archivo de coq *Prop_LC.v* y *Defs_LC.v*  así como los archivos correspondientes *.vo , .vok, .vos .glob, .aux*. En *Prop_LC.v* se plantean los ejercicios de las secciones 3 y 4. En *Defs_LC.v* se planten las definición del operador de cotenabilidad así como su notación y varias tácticas. Una de estás tácticas precisa de un lema el cual también es enunciado y probado en este script. 
4. **Examples** : esta carpeta contiene el archivo de coq *Props_Examples.v* donde se plantean los ejercicios de la sección 5 así como los archivos correspondientes *.vo , .vok, .vos .glob, .aux*. No se precisó de tácticas ni definiciones. 

### Dependencias 
Los archivos *Prop_LM.V* y *Prop_LI.v* no tienen dependencias ni importan bibliotecas. El archivo de *Defs_LC.v* importa la biblioteca nativa de Coq *Classical*. El script *Props_LC.v* depende del *Defs_LC.v* y por tanto ocupa la biblioteca de *Classical*. El script de *Props_Examples.v* importa el script de *Props_LC* y por tanto utiliza 
*Classical* y *Defs_LC.v*. 

## Nota 
Se observó que el operador de cotenabilidad es equivalente al operador de conjunción. Se consideró en plantear la equivalencia y probar los ejericios correspondientes explotando esta equivalencia. Muchas de las propiedades solicitadas en su equivalente en conjunción se encuentren demostradas en la biblioteca predetermianda. Esto puede llevar a soluciones potencialmente más cortas. No obstante, se omitió esta idea pues se consideró que sobrepasa el objetivo del ejercicio de manejar el operador mediante tácticas.