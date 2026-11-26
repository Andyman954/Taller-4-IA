"""Puntos 1–3. Retroceso, consistencia de arcos y heurísticas."""
from collections import deque
from models.csp import SearchTrace, copy_domains


def backtracking_search(csp, domains=None, select_variable=None,
                        order_values=None, trace=None):
    """Punto 1: retorna {tarea: franja} o None si no hay solución.

    Entradas: csp representa el problema; domains contiene los dominios vigentes,
    reducidos por AC-3 cuando corresponde.
    csp.variables contiene los identificadores de las tareas, en orden.
    domains es {tarea: [franjas enteras]}; assignment es {tarea: franja}.
    El bloque por completar define expand(assignment).

    Tips:
    - choose(csp, assignment, domains) retorna una tarea pendiente;
      ordered(csp, x, assignment, domains) retorna sus valores en orden.
    - consistent(x, valor, assignment) retorna si el candidato es compatible
      con la asignación parcial; es el comprobador suministrado para este bloque.
    - search(nueva_asignacion) es la llamada recursiva suministrada. Recibe
      una asignación independiente y retorna una solución completa o None.
    """
    trace = trace if trace is not None else SearchTrace(False)
    domains = copy_domains(csp.domains if domains is None else domains)
    choose = select_variable or (lambda p, a, d: next(x for x in p.variables if x not in a))
    ordering = order_values or (lambda p, x, a, d: list(d[x]))

    # Registra las decisiones y los cambios de la búsqueda.
    def snapshot(assignment):
        return {x: [assignment[x]] if x in assignment else list(domains[x])
                for x in csp.variables}

    def ordered(problem, variable, assignment, current_domains):
        values = ordering(problem, variable, assignment, current_domains)
        trace.record('select', f'Elegir {variable}. Orden de valores: {values}.',
                     assignment, snapshot(assignment) if trace.enabled else domains, variable)
        return values

    def consistent(variable, value, assignment):
        current = snapshot(assignment) if trace.enabled else domains
        trace.attempt(assignment, current, variable, value)
        valid = csp.consistent(variable, value, assignment)
        if valid and trace.enabled:
            child = {**assignment, variable: value}
            trace.record('assign', f'Asignar {variable} a la franja {value}.',
                         child, snapshot(child), variable, value)
        elif not valid:
            trace.record('reject', 'El valor entra en conflicto con una tarea asignada.',
                         assignment, current, variable, value)
        return valid

    def search(assignment):
        result = expand(assignment)
        if result is None and len(assignment) < len(csp.variables):
            trace.fail(assignment, snapshot(assignment) if trace.enabled else domains)
            if assignment and trace.enabled:
                variable = next(reversed(assignment))
                parent = {x: v for x, v in assignment.items() if x != variable}
                trace.restore(parent, snapshot(parent), variable)
        return result

    def expand(assignment):
      #primero debemos revisar el caso base, en este caso si todas las variables tienen una asignacion
      if len(csp.variables) == len(assignment):
        #si todas las variables estan asignadas entonces solo debemos retornarlas
        return assignment
      
      #si faltan variables por asignar entonces debemos ver cual es la proxima tarea pendiente 
      tareaPendiente=choose(csp, assignment, domains)
      #tambien necesitamos saber cual es el dominio de esa tarea
      variablesTarea=ordered(csp, tareaPendiente, assignment, domains)
      #ahora empezamos a probar asignaciones
      for variable in variablesTarea:
        #revisamos si variable es consistente
        if consistent(tareaPendiente, variable, assignment):
          #si es consistente, creamos una copia de assignment, le agregamos la asignacion nueva y llamamos search()
          copiaAssignment = {}
          #loop para crear una copia 
          for i in assignment:
            copiaAssignment[i]= assignment[i]
          #agregamos la asignacion a la copia 
          copiaAssignment[tareaPendiente] = variable 
          #llamamos search para continuar con la recursion
          resultado = search(copiaAssignment)
          if resultado is not None:
            return resultado
          
      return None
    
    
    # FIN DEL BLOQUE DEL ESTUDIANTE

    return search({})


def revise(csp, x, y, domains):
    """Punto 2: revisa X→Y modificando domains[x].

    Retorna True únicamente si cambia ese dominio; False en caso contrario.

    Tips:
    - x e y son identificadores de tareas; domains[x] y domains[y] son listas.
    - csp.compatible(x, valor_x, y, valor_y) comprueba las restricciones
      entre ese par de tareas, respetando la dirección de las precedencias.
    - Si elimina elementos mientras recorre una lista, itere sobre una copia.
    """
    #Creamos una copia para iterar sobre ella
    copiaDominioX=[]
    for i in domains[x]:
      copiaDominioX.append(i)
      
    #Creamos una variable que nos dira si cambiamos el dominio
    cambioDominio=False
    
    #Comenzamos un loop sobre todos los valores del dominio de x
    for i in copiaDominioX:
      #Creamos una variable para ver si algun valor del dominio de y le sirve
      tieneSoporte=False
      #Comenzamos un loop para probar cada valor del dominio x contra cada valor
      #del dominio y 
      for j in domains[y]:
        #revisamos si el valor de x es comapitible con el de y
        if (csp.compatible(x, i, y, j)):
          #Si ALGUN valor es comaptible se queda
          tieneSoporte=True
      #Si ningun valor fue compatible
      if tieneSoporte==False:
        #Quitamos el valor del dominio original
        domains[x].remove(i)
        #cambiamos la variable para retornar el cambio
        cambioDominio=True
    
    
    return cambioDominio
    # FIN DEL BLOQUE DEL ESTUDIANTE


def ac3(csp, domains):
    """Punto 2: reduce domains; retorna False si detecta un dominio vacío.

    Un retorno True indica consistencia de arcos, no garantiza una solución.

    Tips:
    - Cada arco es un par (x, y) de identificadores de tareas.
      csp.neighbors[x] contiene los vecinos de x.
    - revise(csp, x, y, domains) retorna si modificó domains[x].
    """
    #Creamos una cola, esta va a tener todas las tareas que hay que revisar
    cola=[]
    #ponemos todos los arcos en la cola como una tupla (ID_1, ID_2)
    for tarea in domains.keys():
      for vecino in csp.neighbors[tarea]:
        cola.append((tarea,vecino))
      
    #Empezamos la revision AC-3, hasta que la cola no este vacia seguiremos 
    #este loop:
    while len(cola)>0:
      #Sacamos el primer valor de la cola
      tupla=cola.pop(0)
      #Usamos revise() para modificar los dominios necesarios
      if revise(csp,tupla[0],tupla[1],domains):
        #Si tuvimos que modificar el dominio, agregamos el arco en
        #en direccion opuesta a la cola
        cola.append((tupla[1],tupla[0]))
    
    #Ahora comprobamos si los dominios no sean vacios
    for dominio in domains.values():
      if len(dominio)==0:
        return False
      
    return True
    # FIN DEL BLOQUE DEL ESTUDIANTE


def select_unassigned_variable(csp, assignment, domains):
    """Punto 3: retorna el identificador de la variable elegida por MRV y grado.

    Tips:
    - csp.consistent(x, valor, assignment) comprueba si un candidato es
      compatible con la asignacion parcial. Los dominios deben conservarse.
    - csp.neighbors[x] contiene sus vecinos; csp.variables conserva el orden
      original para los desempates.
    """
    
    #MRV = Minimum Remaining Values
    
    #Primero debemos filtar por los valores consistentes:
    #Crearemos un diccionario donde las llaves son tareas y los valores
    #su tamano de dominio
    dominiosConsistenes = {}
    #Hacemos un for loop para filtrar los dominios
    for tarea in csp.variables:
      #guardamos cada tarea no asignada en el dict con una lista 
      if not (tarea in assignment):
        dominiosConsistenes[tarea]=0
        
      for valor in domains[tarea]:
        #Cada valor valido se guarda en el dict
        if tarea not in assignment:
          if csp.consistent(tarea, valor, assignment):
            dominiosConsistenes[tarea] += 1
          
    #ahora haremos MRV sobre dominiosConsistentes
    
    
    #Creamos las variables para encontrar el dominio mas pequeño
    minTarea = None
    minDominio = float("inf")
    
    #empezamos un ciclo donde buscamos el dominio mas pequeño
    for tarea, tamanoDominio in dominiosConsistenes.items():
      #Si el dominio es menor que el "menor" entonces se actualiza 
      if tamanoDominio < minDominio:
        minTarea = tarea
        minDominio = tamanoDominio
        #Si empatan se cuentan los vecinos no asignados, el que tiene mas 
        #queda como min
      elif tamanoDominio == minDominio:
        vecinosTarea = 0
        vecinosMin = 0
        for vecino in csp.neighbors[tarea]:
          if not (vecino in assignment):
            vecinosTarea += 1
        
        for vecino in csp.neighbors[minTarea]:
          if not (vecino in assignment):
            vecinosMin += 1
        #En esta condición queda el desempate de orden
        #Si empatan, min no se actualiza y queda el valor antiguo 
        #como min
        if vecinosTarea > vecinosMin:
          minTarea = tarea
          minDominio = tamanoDominio
          
    return minTarea
      
    
    
    
    
    # FIN DEL BLOQUE DEL ESTUDIANTE


def order_domain_values(csp, variable, assignment, domains):
    """Punto 3: retorna los valores compatibles ordenados por LCV.

    Retorne una lista nueva sin modificar domains y conserve el orden original
    en los empates.

    Tips:
    - Use valores de domains compatibles con assignment, tanto para los
      candidatos como para los vecinos pendientes; compruébelos con
      csp.consistent(x, valor, assignment).
    - csp.compatible(variable, valor, vecino, valor_vecino) comprueba cada par
      sin modificar los dominios.
    """
    #valoresTarea será in dict que tiene los valores de la variable
    #como llave y la cantidad de valores descartados como valor
    valoresTarea= {}
    
    #llenamos valoresTarea solo de los valores consistentes con 
    #la asignacion parcial
    for valor in domains[variable]:
      if csp.consistent(variable, valor, assignment):
        valoresTarea[valor] = 0
    
    #creamos un dict donde tenemos los vecinos no asignados como
    #llaves y una lista de sus valores compatibles con la asignacion
    #parcial como los valores
    vecinos= {}
    
    #pasamso por todos los vecinos viendo si estan asignados
    for vecino in csp.neighbors[variable]:
      if vecino not in assignment:
        #pasamos por los valores de cada vecino agregando los valores
        #consitentes con la asignacion a la lista de ese vecino
        for valor in domains[vecino]:
          if csp.consistent(vecino, valor, assignment):
            if vecino in vecinos:
              vecinos[vecino].append(valor)
            else:
              vecinos[vecino] = [valor]
              
    #pasamos por cada valor de la variable, y por cada uno
    #revisamos cada vecino y cadda vez que los valores 
    #no son compatibles le sumamos 1 al valor en el dict
    for valorTarea in valoresTarea.keys():
      for vecino  in vecinos.keys():
        for valorVecino in vecinos[vecino]:
          if not csp.compatible(variable, valorTarea, vecino, valorVecino):
            valoresTarea[valorTarea] += 1
    
    #debemos organizar los valores por LCV
    
    listaLCV =[]
    
    while len(valoresTarea)>0:
      minValor = None
      minDescartados = float("inf")
      
      for valor, numDescartados in valoresTarea.items():
        if minDescartados > numDescartados:
          minDescartados = numDescartados
          minValor = valor
      
      listaLCV.append(minValor)
      valoresTarea.pop(minValor)
    
    return listaLCV
        
    # FIN DEL BLOQUE DEL ESTUDIANTE
