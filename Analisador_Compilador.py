"""
ANALIZADOR SEMÁNTICO CON GENERACIÓN DE CÓDIGO
"""

import ply.lex as lex
import ply.yacc as yacc
import tkinter as tk
from tkinter import scrolledtext, ttk, filedialog
import re

# ================= DEFINICIÓN DE TOKENS =================
tokens = (
    'PROG','TIPO','TIPO_INT','TIPO_CAD','TIPO_BOOL', 'DECL', 'INICIO', 'FIN',
    'LEERDIG', 'IMPDIG', 'LEERCAD', 'IMPCAD',
    'LEERBOOL', 'IMPBOOL', 'FALS', 'VERD', 'SI',
    'SINO', 'PARA', 'MIENTRAS', 'UNION', 'INTER',
    'IN', 'OR', 'AND', 'NOT', 'PC', 'COMA', 'MAS',
    'MENOS', 'MUL', 'DIV', 'ASIG', 'PAREN', 'TESIS',
    'SIGMENOR', 'SIGMAYOR', 'IGUAL', 'SIGDIF',
    'ID', 'CINT', 'ERROR', 'CAD', 'ERROR_IDENTIFICADOR', 'ERROR_IDENTIFICADOR_SIM'
)

# Diccionario de palabras reservadas
reservadas = {
    'pf2024': ('PROG', 0),
    'Inicio': ('INICIO', 5),
    'Fin': ('FIN', 6),
    'Int': ('TIPO_INT', 1),
    'decl': ('DECL', 4),
    'Cad': ('TIPO_CAD', 2),
    'Bool': ('TIPO_BOOL', 3),
    'leerdig': ('LEERDIG', 7),
    'impdig': ('IMPDIG', 8),
    'Leercad': ('LEERCAD', 9),
    'impcad': ('IMPCAD', 10),
    'leerbol': ('LEERBOOL', 11),
    'Impbool': ('IMPBOOL', 12),
    'falso': ('FALS', 13),
    'verdadero': ('VERD', 14),
    'si': ('SI', 15),
    'sino': ('SINO', 16),
    'para': ('PARA', 17),
    'mientras': ('MIENTRAS', 18),
    'union': ('UNION', 19),
    'inter': ('INTER', 20),
    'in': ('IN', 21),
    'or': ('OR', 22),
    'and': ('AND', 23),
    'not': ('NOT', 24)
}

# ================= TOKENS SIMPLES =================
t_PC = r';'
t_COMA = r','
t_MAS = r'\+'
t_MENOS = r'-'
t_MUL = r'\*'
t_DIV = r'/'
t_ASIG = r':='
t_PAREN = r'\('
t_TESIS = r'\)'
t_SIGMENOR = r'<'
t_SIGMAYOR = r'>'
t_IGUAL = r'='
t_SIGDIF = r'<>'

# ================= VARIABLES GLOBALES =================
errores = []
errores_semanticos = []
tabla_simbolos = []
contador_simbolos = 1
arboles_operaciones = []
t_ignore = ' \t'
lineas_codigo = []
tabla_tipos = {}
temp_counter = 0
cuadruplos_globales = []

# ================= CLASES PARA ANÁLISIS SEMÁNTICO =================

class ErrorSemantico:
    def __init__(self, linea, tipo, descripcion, contexto, sugerencia=None):
        self.linea = linea
        self.tipo = tipo
        self.descripcion = descripcion
        self.contexto = contexto
        self.sugerencia = sugerencia

class Variable:
    def __init__(self, nombre, tipo, linea_declaracion, inicializada=False):
        self.nombre = nombre
        self.tipo = tipo
        self.linea_declaracion = linea_declaracion
        self.inicializada = inicializada
        self.usada = False
        self.lineas_uso = []
        self.valor = None

class AnalizadorSemantico:
    def __init__(self):
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1
        
    def reiniciar(self):
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1

    def declarar_variable(self, nombre, tipo, linea):
        if nombre in self.variables:
            error = ErrorSemantico(
                linea=linea,
                tipo="VARIABLE_DUPLICADA",
                descripcion=f"La variable '{nombre}' ya fue declarada anteriormente",
                contexto=f"Primera declaración en línea {self.variables[nombre].linea_declaracion}",
                sugerencia=f"Use un nombre diferente o elimine la declaración duplicada"
            )
            errores_semanticos.append(error)
        else:
            self.variables[nombre] = Variable(nombre, tipo, linea)
            self.variables_declaradas.add(nombre)
    
    def usar_variable(self, nombre, linea):
        if nombre not in self.variables:
            error = ErrorSemantico(
                linea=linea,
                tipo="VARIABLE_NO_DECLARADA",
                descripcion=f"La variable '{nombre}' no ha sido declarada",
                contexto=f"Se intenta usar '{nombre}' sin declaración previa",
                sugerencia=f"Declare la variable '{nombre}' en la sección 'decl' antes de usarla"
            )
            errores_semanticos.append(error)
            return None
        else:
            self.variables[nombre].usada = True
            self.variables[nombre].lineas_uso.append(linea)
            self.variables_utilizadas.add(nombre)
            return self.variables[nombre]
    
    def asignar_variable(self, nombre, tipo_expresion, linea):
        variable = self.usar_variable(nombre, linea)
        if variable:
            if tipo_expresion and variable.tipo != tipo_expresion:
                error = ErrorSemantico(
                    linea=linea,
                    tipo="INCOMPATIBILIDAD_TIPOS",
                    descripcion=f"Incompatibilidad de tipos en asignación",
                    contexto=f"Se intenta asignar tipo '{tipo_expresion}' a variable '{nombre}' de tipo '{variable.tipo}'",
                    sugerencia=f"Verifique que la expresión sea compatible con el tipo '{variable.tipo}'"
                )
                errores_semanticos.append(error)
            variable.inicializada = True
    
    def verificar_operacion_aritmetica(self, operandos, operador, linea):
        tipo_esperado = "Int"
        for operando in operandos:
            if isinstance(operando, str) and operando in self.variables:
                variable = self.variables[operando]
                if variable.tipo != tipo_esperado:
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="OPERACION_TIPO_INVALIDO",
                        descripcion=f"Operación aritmética '{operador}' no válida para tipo '{variable.tipo}'",
                        contexto=f"Variable '{operando}' de tipo '{variable.tipo}' en operación aritmética",
                        sugerencia=f"Use variables de tipo '{tipo_esperado}' en operaciones aritméticas"
                    )
                    errores_semanticos.append(error)
    
    def verificar_variables_no_utilizadas(self):
        for nombre, variable in self.variables.items():
            if not variable.usada:
                error = ErrorSemantico(
                    linea=variable.linea_declaracion,
                    tipo="VARIABLE_NO_UTILIZADA",
                    descripcion=f"La variable '{nombre}' fue declarada pero nunca utilizada",
                    contexto=f"Variable '{nombre}' de tipo '{variable.tipo}' declarada en línea {variable.linea_declaracion}",
                    sugerencia=f"Elimine la declaración de '{nombre}' si no la necesita, o úsela en el código"
                )
                errores_semanticos.append(error)
    
    def verificar_variables_no_inicializadas(self):
        for nombre, variable in self.variables.items():
            if variable.usada and not variable.inicializada:
                error = ErrorSemantico(
                    linea=variable.lineas_uso[0] if variable.lineas_uso else variable.linea_declaracion,
                    tipo="VARIABLE_NO_INICIALIZADA",
                    descripcion=f"La variable '{nombre}' se usa sin haber sido inicializada",
                    contexto=f"Variable '{nombre}' usada en líneas {variable.lineas_uso} sin asignación previa",
                    sugerencia=f"Asigne un valor a '{nombre}' antes de usarla"
                )
                errores_semanticos.append(error)

analizador_sem = AnalizadorSemantico()

# ================= CLASES AUXILIARES =================
class NodoOperacion:
    def __init__(self, tipo, valor=None, izquierdo=None, derecho=None, linea=None):
        self.tipo = tipo
        self.valor = valor
        self.izquierdo = izquierdo
        self.derecho = derecho
        self.linea = linea or 1
        self.tipo_dato = None

class SimboloTabla:
    def __init__(self, lexema, token, referencia=None):
        global contador_simbolos
        self.numero = contador_simbolos
        self.lexema = lexema
        self.token = token
        self.referencia = referencia
        contador_simbolos += 1

# ================= FUNCIONES AUXILIARES =================
def agregar_simbolo(lexema, token, referencia=None):
    for simbolo in tabla_simbolos:
        if simbolo.lexema == lexema and simbolo.token == token:
            return simbolo
    nuevo_simbolo = SimboloTabla(lexema, token, referencia)
    tabla_simbolos.append(nuevo_simbolo)
    return nuevo_simbolo

def reiniciar_datos():
    global errores, errores_semanticos, tabla_simbolos, contador_simbolos, arboles_operaciones, lineas_codigo, tabla_tipos, temp_counter, cuadruplos_globales
    errores = []
    errores_semanticos = []
    tabla_simbolos = []
    contador_simbolos = 1
    arboles_operaciones = []
    lineas_codigo = []
    tabla_tipos = {}
    temp_counter = 0
    cuadruplos_globales = []
    analizador_sem.reiniciar()

def obtener_linea_actual(p):
    try:
        if hasattr(p, 'lineno'):
            if hasattr(p.lineno, '__call__'):
                return p.lineno(1) if len(p) > 1 else 1
            else:
                return p.lineno
        elif len(p) > 1 and hasattr(p.slice[1], 'lineno'):
            return p.slice[1].lineno
        else:
            return 1
    except (AttributeError, IndexError):
        return 1

# ================= FUNCIONES DE TOKENS =================

def t_CINT(tok):
    r'\d+'
    tok.value = int(tok.value)
    return tok

def t_CAD(tok):
    r'"[^"]*"'
    return tok

def t_ID(t):
    r'[a-zA-Z][a-zA-Z0-9_]*'
    if t.value in reservadas:
        token_info = reservadas[t.value]
        t.type = token_info[0]
        t.ref = token_info[1]
    else:
        t.type = 'ID'
        t.ref = None
    return t

def t_ERROR_IDENTIFICADOR_NUM(t):
    r'\d+[a-zA-Z_]+[a-zA-Z0-9_]*'
    t.type = 'ERROR'
    errores.append({
        'line': t.lineno,
        'value': t.value,
        'type': 'ERROR_IDENTIFICADOR',
        'desc': 'Los identificadores no pueden empezar con números'
    })
    return t

def t_ERROR_IDENTIFICADOR(t):
    r'[a-zA-Z_][a-zA-Z0-9_]*[#$%&!]+[a-zA-Z0-9_]*|[a-zA-Z_]*[#$%&!]+[a-zA-Z0-9_]*'
    t.type = 'ERROR'
    errores.append({
        'line': t.lineno,
        'value': t.value,
        'type': 'ERROR_IDENTIFICADOR',
        'desc': 'Los identificadores solo pueden contener letras, números y guiones bajos'
    })
    return t

def t_newline(tok):
    r'\n+'
    tok.lexer.lineno += len(tok.value)

def t_COMENTARIO(tok):
    r'/\*[^*]*\*+(?:[^/*][^*]*\*+)*/|//.*'
    tok.lexer.lineno += tok.value.count('\n')
    pass

def t_error(t):
    errores.append({
        'line': t.lineno,
        'value': t.value[0],
        'type': 'ERROR_LEXICO',
        'desc': f'Carácter ilegal "{t.value[0]}"'
    })
    t.lexer.skip(1)

analizador_lexico = lex.lex()

# ================= ANALIZADOR SINTÁCTICO =================

precedence = (
    ('left', 'MAS', 'MENOS'),
    ('left', 'MUL', 'DIV'),
    ('right', 'UMINUS'),
)

# ================= REGLAS GRAMATICALES =================

def p_programa(p):
    '''programa : PROG ID programa_decl'''
    agregar_simbolo(p[1], 'PROG', 'Palabra clave del programa')
    agregar_simbolo(p[2], 'ID', 'Nombre del programa')
    analizador_sem.verificar_variables_no_utilizadas()
    analizador_sem.verificar_variables_no_inicializadas()

def p_programa_decl(p):
    '''programa_decl : declaraciones cuerpo_programa
                    | cuerpo_programa'''
    pass

def p_declaraciones(p):
    '''declaraciones : DECL lista_declaraciones'''
    agregar_simbolo(p[1], 'DECL', 'Sección de declaraciones')

def p_lista_declaraciones(p):
    '''lista_declaraciones : declaracion lista_declaraciones
                          | declaracion'''
    pass

def p_declaracion(p):
    '''declaracion : tipo lista_variables PC'''
    agregar_simbolo(';', 'PC', 'Fin de declaración')

def p_tipo(p):
    '''tipo : TIPO_INT
           | TIPO_CAD
           | TIPO_BOOL'''
    if p[1] == 'Int':
        agregar_simbolo('Int', 'TIPO_INT', 'Tipo de dato entero')
        analizador_sem.tipo_actual = 'Int'
    elif p[1] == 'Cad':
        agregar_simbolo('Cad', 'TIPO_CAD', 'Tipo de dato cadena')
        analizador_sem.tipo_actual = 'Cad'
    elif p[1] == 'Bool':
        agregar_simbolo('Bool', 'TIPO_BOOL', 'Tipo de dato booleano')
        analizador_sem.tipo_actual = 'Bool'

def p_lista_variables(p):
    '''lista_variables : ID COMA lista_variables
                      | ID'''
    linea = obtener_linea_actual(p)
    
    if len(p) == 2:
        agregar_simbolo(p[1], 'ID', 'Variable')
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)
    else:
        agregar_simbolo(p[1], 'ID', 'Variable')
        agregar_simbolo(',', 'COMA', 'Separador de variables')
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)

def p_cuerpo_programa(p):
    '''cuerpo_programa : INICIO instrucciones FIN'''
    agregar_simbolo('Inicio', 'INICIO', 'Inicio del programa')
    agregar_simbolo('Fin', 'FIN', 'Fin del programa')

def p_instrucciones(p):
    '''instrucciones : instruccion instrucciones
                    | instruccion'''
    pass

def p_instruccion(p):
    '''instruccion : asignacion
                  | llamada_funcion'''
    pass

def p_asignacion(p):
    '''asignacion : ID ASIG expresion PC'''
    linea = obtener_linea_actual(p)
    
    agregar_simbolo(p[1], 'ID', 'Variable en asignación')
    agregar_simbolo(':=', 'ASIG', 'Operador de asignación')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')
    
    tipo_expresion = None
    if p[3]:
        tipo_expresion = getattr(p[3], 'tipo_dato', 'Int')
    
    analizador_sem.asignar_variable(p[1], tipo_expresion, linea)
    
    if p[3] and hasattr(p[3], 'tipo') and p[3].tipo in ['operacion', 'termino', 'ID']:
        valor, tipo_eval = evaluar_nodo(p[3])
        var = analizador_sem.variables.get(p[1])
        if valor is not None and var is not None:
            var.valor = valor
            var.inicializada = True

        resultado_operando, quads = generar_cuadruplos_desde_nodo(p[3], [])

        asign_dest = p[1]
        if resultado_operando is not None:
            quads.append((':=', resultado_operando, None, asign_dest))

        cuadruplos_globales.extend(quads)

        arboles_operaciones.append({
            'variable': p[1],
            'expresion': p[3],
            'linea': linea,
            'resultado': valor,
            'tipo_resultado': tipo_eval,
            'cuadruplos': quads
        })

def p_expresion_binaria(p):
    '''expresion : expresion MAS expresion
                | expresion MENOS expresion
                | expresion MUL expresion
                | expresion DIV expresion'''
    linea = obtener_linea_actual(p)
    
    operandos = []
    if hasattr(p[1], 'valor') and isinstance(p[1].valor, str):
        operandos.append(p[1].valor)
    if hasattr(p[3], 'valor') and isinstance(p[3].valor, str):
        operandos.append(p[3].valor)
    
    analizador_sem.verificar_operacion_aritmetica(operandos, p[2], linea)
    
    if p[2] == '+':
        agregar_simbolo('+', 'MAS', 'Operador suma')
        p[0] = NodoOperacion('operacion', '+', p[1], p[3], linea)
    elif p[2] == '-':
        agregar_simbolo('-', 'MENOS', 'Operador resta')
        p[0] = NodoOperacion('operacion', '-', p[1], p[3], linea)
    elif p[2] == '*':
        agregar_simbolo('*', 'MUL', 'Operador multiplicación')
        p[0] = NodoOperacion('operacion', '*', p[1], p[3], linea)
    elif p[2] == '/':
        agregar_simbolo('/', 'DIV', 'Operador división')
        p[0] = NodoOperacion('operacion', '/', p[1], p[3], linea)
        
        if hasattr(p[3], 'valor') and p[3].valor == '0':
            error = ErrorSemantico(
                linea=linea,
                tipo="DIVISION_POR_CERO",
                descripcion="Posible división por cero",
                contexto=f"División por constante cero en línea {linea}",
                sugerencia="Verifique que el divisor no sea cero"
            )
            errores_semanticos.append(error)
    
    p[0].tipo_dato = 'Int'

def p_expresion_unaria(p):
    '''expresion : MENOS expresion %prec UMINUS'''
    linea = obtener_linea_actual(p)
    agregar_simbolo('-', 'MENOS', 'Operador menos unario')
    p[0] = NodoOperacion('operacion', '-', None, p[2], linea)
    p[0].tipo_dato = 'Int'

def p_expresion_parentesis(p):
    '''expresion : PAREN expresion TESIS'''
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    p[0] = p[2]

def p_expresion_factor(p):
    '''expresion : ID
                | CINT'''
    linea = obtener_linea_actual(p)
    
    if isinstance(p[1], int):
        agregar_simbolo(str(p[1]), 'CINT', 'Constante entera')
        p[0] = NodoOperacion('termino', str(p[1]), None, None, linea)
        p[0].tipo_dato = 'Int'
    else:
        agregar_simbolo(p[1], 'ID', 'Variable en expresión')
        variable = analizador_sem.usar_variable(p[1], linea)
        p[0] = NodoOperacion('ID', p[1], None, None, linea)
        p[0].tipo_dato = variable.tipo if variable else 'Int'

def p_llamada_funcion(p):
    '''llamada_funcion : IMPCAD PAREN parametro TESIS PC
                      | LEERDIG PAREN ID TESIS PC'''
    linea = obtener_linea_actual(p)
    
    if p[1] == 'impcad':
        agregar_simbolo('impcad', 'IMPCAD', 'Función imprimir cadena')
        param = p[3] if p[3] else "None"
        cuadruplos_globales.append(('impcad', param, None, None))
        
        if p[3] is not None:
            if not (isinstance(p[3], str) and p[3].startswith('"') and p[3].endswith('"')):
                variable = analizador_sem.usar_variable(p[3], linea)
                if variable and variable.tipo != 'Cad':
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="PARAMETRO_TIPO_INCORRECTO",
                        descripcion=f"La función 'impcad' requiere parámetro de tipo 'Cad'",
                        contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'impcad'",
                        sugerencia="Use una variable de tipo 'Cad' o una cadena literal"
                    )
                    errores_semanticos.append(error)
        else:
            error = ErrorSemantico(
                linea=linea,
                tipo="PARAMETRO_FALTANTE",
                descripcion="La función 'impcad' requiere un parámetro",
                contexto="Llamada a 'impcad' sin parámetro",
                sugerencia="Proporcione una cadena literal o variable de tipo 'Cad'"
            )
            errores_semanticos.append(error)
            
    elif p[1] == 'leerdig':
        agregar_simbolo('leerdig', 'LEERDIG', 'Función leer dígito')
        cuadruplos_globales.append(('leerdig', None, None, p[3]))
        
        if p[3] is not None:
            agregar_simbolo(p[3], 'ID', 'Variable para leer')
            variable = analizador_sem.usar_variable(p[3], linea)
            if variable and variable.tipo != 'Int':
                error = ErrorSemantico(
                    linea=linea,
                    tipo="PARAMETRO_TIPO_INCORRECTO",
                    descripcion=f"La función 'leerdig' requiere variable de tipo 'Int'",
                    contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'leerdig'",
                    sugerencia="Use una variable de tipo 'Int'"
                )
                errores_semanticos.append(error)
            else:
                if variable:
                    variable.inicializada = True
        else:
            error = ErrorSemantico(
                linea=linea,
                tipo="PARAMETRO_FALTANTE",
                descripcion="La función 'leerdig' requiere un parámetro",
                contexto="Llamada a 'leerdig' sin parámetro",
                sugerencia="Proporcione una variable de tipo 'Int'"
            )
            errores_semanticos.append(error)
    
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')

def p_parametro(p):
    '''parametro : CAD
                | ID'''
    if p[1].startswith('"') and p[1].endswith('"'):
        agregar_simbolo(p[1], 'CAD', 'Literal de cadena')
        p[0] = p[1]
    else:
        agregar_simbolo(p[1], 'ID', 'Variable como parámetro')
        p[0] = p[1]

def p_error(p):
    try:
        if p:
            token_descripcion = obtener_descripcion_token(p.type, p.value)
            linea = getattr(p, 'lineno', 'desconocida')
            errores.append({
                'line': linea,
                'value': str(p.value) if p.value is not None else 'None',
                'type': 'ERROR_SINTACTICO',
                'desc': f"Error de sintaxis: se encontró {token_descripcion}"
            })
        else:
            errores.append({
                'line': 'EOF',
                'value': 'EOF',
                'type': 'ERROR_SINTACTICO',
                'desc': "Error de sintaxis: fin de archivo inesperado"
            })
    except Exception as e:
        errores.append({
            'line': 'desconocida',
            'value': 'error_interno',
            'type': 'ERROR_SINTACTICO',
            'desc': "Error de sintaxis: error interno del parser"
        })

def obtener_descripcion_token(tipo_token, valor_token):
    descripciones = {
        'TESIS': 'paréntesis de cierre ")"',
        'PAREN': 'paréntesis de apertura "("',
        'PC': 'punto y coma ";"',
        'ID': f'identificador "{valor_token}"',
        'CINT': f'número "{valor_token}"',
    }
    return descripciones.get(tipo_token, f'token {tipo_token}')

parser = yacc.yacc()

# ================= FUNCIONES PARA EVALUACIÓN =================

def expresion_a_texto(nodo, precedencia_padre=0):
    if nodo is None:
        return ""
    precedencias = {'+': 1, '-': 1, '*': 2, '/': 2}
    if nodo.tipo == 'operacion':
        precedencia_actual = precedencias.get(nodo.valor, 0)
        if nodo.izquierdo is None:
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{nodo.valor}{der_texto}"
        else:
            izq_texto = expresion_a_texto(nodo.izquierdo, precedencia_actual)
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{izq_texto} {nodo.valor} {der_texto}"
        if precedencia_actual < precedencia_padre:
            expresion = f"({expresion})"
        return expresion
    elif nodo.tipo in ('termino', 'ID'):
        return str(nodo.valor)
    return str(nodo.valor)

def imprimir_arbol_operacion(nodo, nivel=0):
    if nodo is None:
        return ""
    indentacion = "  " * nivel
    resultado = ""
    if nodo.tipo == 'operacion':
        resultado += f"{indentacion}operacion: {nodo.valor}\n"
        if nodo.izquierdo:
            resultado += imprimir_arbol_operacion(nodo.izquierdo, nivel + 1)
        if nodo.derecho:
            resultado += imprimir_arbol_operacion(nodo.derecho, nivel + 1)
    elif nodo.tipo == 'termino':
        resultado += f"{indentacion}termino: {nodo.valor}\n"
    elif nodo.tipo == 'ID':
        resultado += f"{indentacion}ID: {nodo.valor}\n"
    return resultado

def evaluar_nodo(nodo):
    if nodo is None:
        return None, None
    if nodo.tipo == 'termino':
        try:
            v = int(nodo.valor)
            return v, 'Int'
        except Exception:
            return None, None
    if nodo.tipo == 'ID':
        nombre = nodo.valor
        var = analizador_sem.variables.get(nombre)
        if var is None or not var.inicializada:
            return None, None
        return var.valor, var.tipo
    if nodo.tipo == 'operacion':
        op = nodo.valor
        if nodo.izquierdo is None:
            rv, rt = evaluar_nodo(nodo.derecho)
            if rv is None or rt != 'Int':
                return None, None
            if op == '-':
                return -rv, 'Int'
            return None, None
        lv, lt = evaluar_nodo(nodo.izquierdo)
        rv, rt = evaluar_nodo(nodo.derecho)
        if lv is None or rv is None or lt != 'Int' or rt != 'Int':
            return None, None
        try:
            if op == '+':
                return lv + rv, 'Int'
            elif op == '-':
                return lv - rv, 'Int'
            elif op == '*':
                return lv * rv, 'Int'
            elif op == '/':
                if rv == 0:
                    return None, None
                return lv // rv, 'Int'
        except Exception:
            return None, None
    return None, None

def nuevo_temp():
    global temp_counter
    temp_counter += 1
    return f"t{temp_counter}"

def generar_cuadruplos_desde_nodo(nodo, quads=None):
    if quads is None:
        quads = []
    if nodo is None:
        return None, quads
    if nodo.tipo == 'termino':
        return nodo.valor, quads
    if nodo.tipo == 'ID':
        return nodo.valor, quads
    if nodo.tipo == 'operacion' and nodo.izquierdo is None:
        op = nodo.valor
        operando_d, quads = generar_cuadruplos_desde_nodo(nodo.derecho, quads)
        t = nuevo_temp()
        quads.append((op, operando_d, None, t))
        return t, quads
    if nodo.tipo == 'operacion':
        op = nodo.valor
        left_operand, quads = generar_cuadruplos_desde_nodo(nodo.izquierdo, quads)
        right_operand, quads = generar_cuadruplos_desde_nodo(nodo.derecho, quads)
        t = nuevo_temp()
        quads.append((op, left_operand, right_operand, t))
        return t, quads
    return None, quads

def generar_arboles_texto():
    if not arboles_operaciones:
        return "No se encontraron operaciones aritméticas en el código."
    resultado = ""
    for i, operacion in enumerate(arboles_operaciones, 1):
        nodo = operacion['expresion']
        expresion_texto = expresion_a_texto(nodo)
        resultado += f"=== Operación {i}: {operacion['variable']} := {expresion_texto} ===\n"
        resultado += f"Línea: {operacion.get('linea', 'N/A')}\n\n"
        resultado += f"Expresión: {expresion_texto}\n\n"
        resultado += f"Árbol sintáctico:\n"
        resultado += imprimir_arbol_operacion(nodo)
        resultado += "\n" + "="*60 + "\n\n"
    return resultado

def generar_resultados_texto():
    resultado = ""
    if not arboles_operaciones:
        resultado += "No hay operaciones para evaluar.\n\n"
    else:
        resultado += "RESULTADOS DE EVALUACIÓN DE OPERACIONES\n"
        resultado += "="*50 + "\n\n"
        for i, op in enumerate(arboles_operaciones, 1):
            nodo = op['expresion']
            infija = expresion_a_texto(nodo)
            res = op.get('resultado')
            resultado += f"{op['variable']} := {infija}\n"
            resultado += f"  Resultado: {res if res is not None else 'No evaluable'}\n"
            resultado += "-"*40 + "\n"
        resultado += "\n"
    resultado += "TABLA DE VARIABLES (VALORES)\n"
    resultado += "="*30 + "\n"
    if analizador_sem.variables:
        resultado += f"{'Variable':<12} {'Tipo':<6} {'Inicializada':<12} {'Valor'}\n"
        resultado += "-"*50 + "\n"
        for nombre, var in analizador_sem.variables.items():
            ini = "Si" if var.inicializada else "No"
            resultado += f"{nombre:<12} {var.tipo:<6} {ini:<12} {var.valor if var.valor is not None else '-'}\n"
    else:
        resultado += "No se declararon variables.\n"
    return resultado

def generar_reporte_semantico():
    if not errores_semanticos and not analizador_sem.variables:
        return "No se realizó análisis semántico."
    resultado = "REPORTE DE ANÁLISIS SEMÁNTICO\n"
    resultado += "="*50 + "\n\n"
    resultado += "1. TABLA DE VARIABLES DECLARADAS:\n"
    resultado += "-"*40 + "\n"
    if analizador_sem.variables:
        resultado += f"{'Variable':<15} {'Tipo':<8} {'Línea':<6} {'Inicial.':<8} {'Usada':<6}\n"
        resultado += "-"*70 + "\n"
        for nombre, var in analizador_sem.variables.items():
            inicializada = "Si" if var.inicializada else "No"
            usada = "Si" if var.usada else "No"
            resultado += f"{nombre:<15} {var.tipo:<8} {var.linea_declaracion:<6} {inicializada:<8} {usada:<6}\n"
    else:
        resultado += "No se encontraron variables declaradas.\n"
    resultado += "\n"
    resultado += "2. ESTADÍSTICAS:\n"
    resultado += "-"*20 + "\n"
    resultado += f"Variables declaradas: {len(analizador_sem.variables)}\n"
    resultado += f"Variables utilizadas: {len(analizador_sem.variables_utilizadas)}\n"
    resultado += f"Errores semánticos: {len(errores_semanticos)}\n\n"
    if errores_semanticos:
        resultado += "3. ERRORES SEMÁNTICOS:\n"
        resultado += "-"*35 + "\n"
        for i, error in enumerate(errores_semanticos, 1):
            resultado += f"Error #{i}:\n"
            resultado += f"  Línea: {error.linea}\n"
            resultado += f"  Tipo: {error.tipo}\n"
            resultado += f"  Descripción: {error.descripcion}\n\n"
    else:
        resultado += "3. No se encontraron errores semánticos.\n\n"
    return resultado

def generar_codigo_fuente():
    if not cuadruplos_globales:
        return "No se generaron cuádruplos.\n"
    resultado = "GENERACIÓN DE CÓDIGO FUENTE\n"
    resultado += "="*60 + "\n\n"
    resultado += "CUÁDRUPLOS GENERADOS:\n"
    resultado += "-"*60 + "\n"
    resultado += f"{'#':<4} {'Operador':<10} {'Arg1':<12} {'Arg2':<12} {'Resultado':<12}\n"
    resultado += "-"*60 + "\n"
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        arg1_str = str(arg1) if arg1 is not None else '-'
        arg2_str = str(arg2) if arg2 is not None else '-'
        res_str = str(res) if res is not None else '-'
        resultado += f"{i:<4} {op:<10} {arg1_str:<12} {arg2_str:<12} {res_str:<12}\n"
    resultado += "\n" + "="*60 + "\n\n"
    resultado += "CÓDIGO ENSAMBLADOR EQUIVALENTE (x86):\n"
    resultado += "-"*60 + "\n"
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        resultado += f"; Cuádruplo {i}\n"
        if op == ':=':
            resultado += f"MOV {res}, {arg1}\n"
        elif op == '+':
            resultado += f"MOV EAX, {arg1}\n"
            resultado += f"ADD EAX, {arg2}\n"
            resultado += f"MOV {res}, EAX\n"
        elif op == '-':
            if arg2 is None:
                resultado += f"MOV EAX, {arg1}\n"
                resultado += f"NEG EAX\n"
                resultado += f"MOV {res}, EAX\n"
            else:
                resultado += f"MOV EAX, {arg1}\n"
                resultado += f"SUB EAX, {arg2}\n"
                resultado += f"MOV {res}, EAX\n"
        elif op == '*':
            resultado += f"MOV EAX, {arg1}\n"
            resultado += f"IMUL EAX, {arg2}\n"
            resultado += f"MOV {res}, EAX\n"
        elif op == '/':
            resultado += f"MOV EAX, {arg1}\n"
            resultado += f"CDQ\n"
            resultado += f"IDIV {arg2}\n"
            resultado += f"MOV {res}, EAX\n"
        elif op == 'impcad':
            resultado += f"PUSH {arg1}\n"
            resultado += f"CALL print_string\n"
        elif op == 'leerdig':
            resultado += f"CALL read_int\n"
            resultado += f"MOV {res}, EAX\n"
        resultado += "\n"
    return resultado

# ================= INTERFAZ GRÁFICA =================
class AnalizadorGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Analizador Completo con Generación de Código - PF2024")
        self.root.geometry("1600x1000")
        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill='both', expand=True, padx=10, pady=10)
        self.frame_principal = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_principal, text="Análisis Principal")
        self.frame_arbol = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_arbol, text="Árboles de Operaciones")
        self.frame_semantico = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_semantico, text="Análisis Semántico")
        self.frame_resultados = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_resultados, text="Resultados")
        self.frame_generacion = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_generacion, text="Generación de Código")
        self.crear_interfaz_principal()
        self.crear_interfaz_arbol()
        self.crear_interfaz_semantico()
        self.crear_interfaz_resultados()
        self.crear_interfaz_generacion()
    
    def crear_interfaz_principal(self):
        main_frame = ttk.Frame(self.frame_principal, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        ttk.Label(main_frame, text="Código fuente:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.codigo_text = scrolledtext.ScrolledText(main_frame, height=15, width=80)
        self.codigo_text.grid(row=1, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=(0, 10))
        codigo_ejemplo = '''pf2024 programa
decl
Int a, b, resultado;
Cad mensaje;

Inicio
a := 5;
b := 3;
resultado := a + b * 2;
mensaje := "Hola Mundo";
impcad(mensaje);
leerdig(a);
Fin'''
        self.codigo_text.insert('1.0', codigo_ejemplo)
        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=2, column=0, columnspan=2, pady=(0, 10))
        ttk.Button(button_frame, text="Analizar", command=self.analizar).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="Limpiar", command=self.limpiar_todo).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="Cargar Archivo", command=self.cargar_archivo).pack(side=tk.LEFT)
        ttk.Label(main_frame, text="Tabla de Símbolos:").grid(row=3, column=0, sticky=tk.W, pady=(10, 5))
        columns = ('No.', 'Lexema', 'Token', 'Referencia')
        self.tabla_tree = ttk.Treeview(main_frame, columns=columns, show='headings', height=12)
        for col in columns:
            self.tabla_tree.heading(col, text=col)
            self.tabla_tree.column(col, width=150)
        self.tabla_tree.grid(row=4, column=0, columnspan=2, sticky=(tk.W, tk.E))
        scrollbar = ttk.Scrollbar(main_frame, orient=tk.VERTICAL, command=self.tabla_tree.yview)
        scrollbar.grid(row=4, column=2, sticky=(tk.N, tk.S))
        self.tabla_tree.configure(yscrollcommand=scrollbar.set)
        ttk.Label(main_frame, text="Errores:").grid(row=5, column=0, sticky=tk.W, pady=(10, 5))
        self.errores_text = scrolledtext.ScrolledText(main_frame, height=10, width=80)
        self.errores_text.grid(row=6, column=0, columnspan=2, sticky=(tk.W, tk.E))
        self.frame_principal.columnconfigure(0, weight=1)
        self.frame_principal.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
    
    def crear_interfaz_arbol(self):
        arbol_frame = ttk.Frame(self.frame_arbol, padding="10")
        arbol_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        ttk.Label(arbol_frame, text="Árboles de Operaciones:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.arbol_text = scrolledtext.ScrolledText(arbol_frame, height=40, width=120, font=('Courier', 10))
        self.arbol_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        scrollbar_arbol = ttk.Scrollbar(arbol_frame, orient=tk.VERTICAL, command=self.arbol_text.yview)
        scrollbar_arbol.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.arbol_text.configure(yscrollcommand=scrollbar_arbol.set)
        self.frame_arbol.columnconfigure(0, weight=1)
        self.frame_arbol.rowconfigure(0, weight=1)
        arbol_frame.columnconfigure(0, weight=1)
        arbol_frame.rowconfigure(1, weight=1)
    
    def crear_interfaz_semantico(self):
        sem_frame = ttk.Frame(self.frame_semantico, padding="10")
        sem_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        ttk.Label(sem_frame, text="Análisis Semántico:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.semantico_text = scrolledtext.ScrolledText(sem_frame, height=40, width=120, font=('Courier', 10))
        self.semantico_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        scrollbar_sem = ttk.Scrollbar(sem_frame, orient=tk.VERTICAL, command=self.semantico_text.yview)
        scrollbar_sem.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.semantico_text.configure(yscrollcommand=scrollbar_sem.set)
        self.frame_semantico.columnconfigure(0, weight=1)
        self.frame_semantico.rowconfigure(0, weight=1)
        sem_frame.columnconfigure(0, weight=1)
        sem_frame.rowconfigure(1, weight=1)
    
    def crear_interfaz_resultados(self):
        res_frame = ttk.Frame(self.frame_resultados, padding="10")
        res_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        ttk.Label(res_frame, text="Resultados:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.resultados_text = scrolledtext.ScrolledText(res_frame, height=40, width=120, font=('Courier', 10))
        self.resultados_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        scrollbar_res = ttk.Scrollbar(res_frame, orient=tk.VERTICAL, command=self.resultados_text.yview)
        scrollbar_res.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.resultados_text.configure(yscrollcommand=scrollbar_res.set)
        self.frame_resultados.columnconfigure(0, weight=1)
        self.frame_resultados.rowconfigure(0, weight=1)
        res_frame.columnconfigure(0, weight=1)
        res_frame.rowconfigure(1, weight=1)
    
    def crear_interfaz_generacion(self):
        gen_frame = ttk.Frame(self.frame_generacion, padding="10")
        gen_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        ttk.Label(gen_frame, text="Generación de Código:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.generacion_text = scrolledtext.ScrolledText(gen_frame, height=40, width=120, font=('Courier', 10))
        self.generacion_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        scrollbar_gen = ttk.Scrollbar(gen_frame, orient=tk.VERTICAL, command=self.generacion_text.yview)
        scrollbar_gen.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.generacion_text.configure(yscrollcommand=scrollbar_gen.set)
        self.frame_generacion.columnconfigure(0, weight=1)
        self.frame_generacion.rowconfigure(0, weight=1)
        gen_frame.columnconfigure(0, weight=1)
        gen_frame.rowconfigure(1, weight=1)

    def analizar(self):
        reiniciar_datos()
        self.errores_text.delete('1.0', tk.END)
        self.arbol_text.delete('1.0', tk.END)
        self.semantico_text.delete('1.0', tk.END)
        self.resultados_text.delete('1.0', tk.END)
        self.generacion_text.delete('1.0', tk.END)
        codigo = self.codigo_text.get('1.0', tk.END)
        global lineas_codigo
        lineas_codigo = codigo.split('\n')
        try:
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            parser.parse(lexer=analizador_lexico)
            self.actualizar_tabla()
            self.arbol_text.insert('1.0', generar_arboles_texto())
            self.resultados_text.insert('1.0', generar_resultados_texto())
            self.semantico_text.insert('1.0', generar_reporte_semantico())
            self.generacion_text.insert('1.0', generar_codigo_fuente())
            if errores:
                self.errores_text.insert(tk.END, "ERRORES ENCONTRADOS:\n" + "="*50 + "\n")
                for i, error in enumerate(errores, 1):
                    self.errores_text.insert(tk.END, f"Error #{i}: Línea {error['line']}\n")
                    self.errores_text.insert(tk.END, f"  {error['desc']}\n\n")
            else:
                self.errores_text.insert(tk.END, "No se encontraron errores.\n")
        except Exception as e:
            self.errores_text.insert(tk.END, f"Error: {str(e)}\n")
    
    def actualizar_tabla(self):
        for item in self.tabla_tree.get_children():
            self.tabla_tree.delete(item)
        for simbolo in tabla_simbolos:
            self.tabla_tree.insert('', 'end', values=(
                simbolo.numero, simbolo.lexema, simbolo.token, simbolo.referencia or ''
            ))
    
    def limpiar_todo(self):
        reiniciar_datos()
        self.actualizar_tabla()
        self.errores_text.delete('1.0', tk.END)
        self.arbol_text.delete('1.0', tk.END)
        self.semantico_text.delete('1.0', tk.END)
        self.resultados_text.delete('1.0', tk.END)
        self.generacion_text.delete('1.0', tk.END)
    
    def cargar_archivo(self):
        file_path = filedialog.askopenfilename(
            title="Seleccionar archivo",
            filetypes=[("Archivos PF2024", "*.pf"), ("Todos", "*.*")]
        )
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as file:
                    self.codigo_text.delete('1.0', tk.END)
                    self.codigo_text.insert('1.0', file.read())
            except Exception as e:
                self.errores_text.insert(tk.END, f"Error al cargar: {str(e)}\n")

    def reiniciar_lexer(self):
        analizador_lexico.lineno = 1
        analizador_lexico.lexpos = 0

if __name__ == "__main__":
    print("="*70)
    print("ANALIZADOR COMPLETO CON GENERACIÓN DE CÓDIGO - PF2024")
    print("="*70)
    root = tk.Tk()
    app = AnalizadorGUI(root)
    root.mainloop()