
"""
ANALIZADOR SINTÁCTICO PF2024 - VERSIÓN CORREGIDA
Corrección del error en expresiones con operador + y paréntesis
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
tabla_simbolos = []
contador_simbolos = 1
arboles_operaciones = []
t_ignore = ' \t'

# ================= CLASES =================
class NodoOperacion:
    def __init__(self, tipo, valor=None, izquierdo=None, derecho=None):
        self.tipo = tipo
        self.valor = valor
        self.izquierdo = izquierdo
        self.derecho = derecho
    
    def __str__(self):
        if self.tipo == 'operacion':
            return f"operacion: {self.valor}"
        elif self.tipo == 'termino':
            return f"termino: {self.valor}"
        elif self.tipo == 'ID':
            return f"ID: {self.valor}"
        else:
            return str(self.valor)

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
    global errores, tabla_simbolos, contador_simbolos, arboles_operaciones
    errores = []
    tabla_simbolos = []
    contador_simbolos = 1
    arboles_operaciones = []

# ================= FUNCIONES DE TOKENS (ORDEN CORREGIDO) =================

# PRIMERO: Reconocer números enteros
def t_CINT(tok):
    r'\d+'
    tok.value = int(tok.value)
    return tok

# SEGUNDO: Reconocer cadenas de texto
def t_CAD(tok):
    r'"[^"]*"'
    return tok

# TERCERO: Reconocer identificadores y palabras reservadas
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

# CUARTO: Errores de identificadores que empiezan con número
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

# QUINTO: Errores de identificadores con caracteres especiales
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

# SEXTO: Contar líneas nuevas
def t_newline(tok):
    r'\n+'
    tok.lexer.lineno += len(tok.value)

# SÉPTIMO: Reconocer y omitir comentarios
def t_COMENTARIO(tok):
    r'/\*[^*]*\*+(?:[^/*][^*]*\*+)*/|//.*'
    tok.lexer.lineno += tok.value.count('\n')
    pass

# ÚLTIMO: Manejo de errores léxicos
def t_error(t):
    errores.append({
        'line': t.lineno,
        'value': t.value[0],
        'type': 'ERROR_LEXICO',
        'desc': f'Carácter ilegal "{t.value[0]}"'
    })
    t.lexer.skip(1)

# Construcción del analizador léxico
analizador_lexico = lex.lex()

# ================= ANALIZADOR SINTÁCTICO CORREGIDO =================

# CORRECCIÓN: Precedencia corregida para evitar conflictos
precedence = (
    ('left', 'MAS', 'MENOS'),    # Menor precedencia
    ('left', 'MUL', 'DIV'),      # Mayor precedencia
    ('right', 'UMINUS'),         # Para menos unario
)

# ================= REGLAS GRAMATICALES CORREGIDAS =================

def p_programa(p):
    '''programa : PROG ID programa_decl'''
    agregar_simbolo(p[1], 'PROG', 'Palabra clave del programa')
    agregar_simbolo(p[2], 'ID', 'Nombre del programa')

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
    elif p[1] == 'Cad':
        agregar_simbolo('Cad', 'TIPO_CAD', 'Tipo de dato cadena')
    elif p[1] == 'Bool':
        agregar_simbolo('Bool', 'TIPO_BOOL', 'Tipo de dato booleano')

def p_lista_variables(p):
    '''lista_variables : ID COMA lista_variables
                      | ID'''
    if len(p) == 2:
        agregar_simbolo(p[1], 'ID', 'Variable')
    else:
        agregar_simbolo(p[1], 'ID', 'Variable')
        agregar_simbolo(',', 'COMA', 'Separador de variables')

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
    agregar_simbolo(p[1], 'ID', 'Variable en asignación')
    agregar_simbolo(':=', 'ASIG', 'Operador de asignación')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')
    
    # Guardar la operación aritmética
    if p[3] and hasattr(p[3], 'tipo') and p[3].tipo in ['operacion', 'termino', 'ID']:
        arboles_operaciones.append({
            'variable': p[1],
            'expresion': p[3]
        })

# CORRECCIÓN PRINCIPAL: Reglas de expresión simplificadas y corregidas
def p_expresion_binaria(p):
    '''expresion : expresion MAS expresion
                | expresion MENOS expresion
                | expresion MUL expresion
                | expresion DIV expresion'''
    # Esta regla maneja todas las operaciones binarias de forma uniforme
    if p[2] == '+':
        agregar_simbolo('+', 'MAS', 'Operador suma')
        p[0] = NodoOperacion('operacion', '+', p[1], p[3])
    elif p[2] == '-':
        agregar_simbolo('-', 'MENOS', 'Operador resta')
        p[0] = NodoOperacion('operacion', '-', p[1], p[3])
    elif p[2] == '*':
        agregar_simbolo('*', 'MUL', 'Operador multiplicación')
        p[0] = NodoOperacion('operacion', '*', p[1], p[3])
    elif p[2] == '/':
        agregar_simbolo('/', 'DIV', 'Operador división')
        p[0] = NodoOperacion('operacion', '/', p[1], p[3])

def p_expresion_unaria(p):
    '''expresion : MENOS expresion %prec UMINUS'''
    # Manejo del menos unario
    agregar_simbolo('-', 'MENOS', 'Operador menos unario')
    p[0] = NodoOperacion('operacion', '-', None, p[2])

def p_expresion_parentesis(p):
    '''expresion : PAREN expresion TESIS'''
    # CORRECCIÓN: Manejo correcto de paréntesis
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    p[0] = p[2]  # La expresión dentro de paréntesis

def p_expresion_factor(p):
    '''expresion : ID
                | CINT'''
    # Factores básicos: identificadores y números
    if isinstance(p[1], int):
        agregar_simbolo(str(p[1]), 'CINT', 'Constante entera')
        p[0] = NodoOperacion('termino', str(p[1]))
    else:
        agregar_simbolo(p[1], 'ID', 'Variable en expresión')
        p[0] = NodoOperacion('ID', p[1])

def p_llamada_funcion(p):
    '''llamada_funcion : IMPCAD PAREN parametro TESIS PC
                      | LEERDIG PAREN ID TESIS PC'''
    if p[1] == 'impcad':
        agregar_simbolo('impcad', 'IMPCAD', 'Función imprimir cadena')
    elif p[1] == 'leerdig':
        agregar_simbolo('leerdig', 'LEERDIG', 'Función leer dígito')
        agregar_simbolo(p[3], 'ID', 'Variable para leer')
    
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')

def p_parametro(p):
    '''parametro : CAD
                | ID'''
    if p[1].startswith('"') and p[1].endswith('"'):
        agregar_simbolo(p[1], 'CAD', 'Literal de cadena')
    else:
        agregar_simbolo(p[1], 'ID', 'Variable como parámetro')

def p_error(p):
    """Manejo de errores sintácticos mejorado"""
    if p:
        token_descripcion = obtener_descripcion_token(p.type, p.value)
        print(f"Error de sintaxis en {token_descripcion} en línea {p.lineno}")
        errores.append({
            'line': p.lineno,
            'value': p.value,
            'type': 'ERROR_SINTACTICO',
            'desc': f"Error de sintaxis: se encontró {token_descripcion}"
        })
    else:
        print("Error de sintaxis: fin de archivo inesperado")
        errores.append({
            'line': 'EOF',
            'value': 'EOF',
            'type': 'ERROR_SINTACTICO',
            'desc': "Error de sintaxis: fin de archivo inesperado"
        })

def obtener_descripcion_token(tipo_token, valor_token):
    """Convierte los tipos de tokens en descripciones más amigables"""
    descripciones = {
        'TESIS': f'paréntesis de cierre ")"',
        'PAREN': f'paréntesis de apertura "("',
        'PC': f'punto y coma ";"',
        'COMA': f'coma ","',
        'MAS': f'operador suma "+"',
        'MENOS': f'operador resta "-"',
        'MUL': f'operador multiplicación "*"',
        'DIV': f'operador división "/"',
        'ASIG': f'operador de asignación ":="',
        'ID': f'identificador "{valor_token}"',
        'CINT': f'número "{valor_token}"',
        'CAD': f'cadena de texto {valor_token}',
        'PROG': f'palabra clave "pf2024"',
        'DECL': f'palabra clave "decl"',
        'INICIO': f'palabra clave "Inicio"',
        'FIN': f'palabra clave "Fin"',
        'TIPO_INT': f'tipo de dato "Int"',
        'TIPO_CAD': f'tipo de dato "Cad"',
        'TIPO_BOOL': f'tipo de dato "Bool"',
        'LEERDIG': f'función "leerdig"',
        'IMPCAD': f'función "impcad"',
    }
    
    if tipo_token in descripciones:
        return descripciones[tipo_token]
    else:
        return f'token {tipo_token} "{valor_token}"'

# Construcción del analizador sintáctico
parser = yacc.yacc()

# ================= FUNCIONES PARA ÁRBOLES =================
def expresion_a_texto(nodo, precedencia_padre=0):
    """Convierte un nodo del árbol a texto"""
    if nodo is None:
        return ""
    
    precedencias = {'+': 1, '-': 1, '*': 2, '/': 2}
    
    if nodo.tipo == 'operacion':
        precedencia_actual = precedencias.get(nodo.valor, 0)
        
        if nodo.izquierdo is None:  # Operador unario
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{nodo.valor}{der_texto}"
        else:  # Operador binario
            izq_texto = expresion_a_texto(nodo.izquierdo, precedencia_actual)
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{izq_texto} {nodo.valor} {der_texto}"
        
        if precedencia_actual < precedencia_padre:
            expresion = f"({expresion})"
        
        return expresion
    elif nodo.tipo == 'termino':
        return str(nodo.valor)
    elif nodo.tipo == 'ID':
        return str(nodo.valor)
    else:
        return str(nodo.valor)

def imprimir_arbol_operacion(nodo, nivel=0):
    """Imprime un árbol de operación de forma jerárquica"""
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

def generar_arboles_texto():
    """Genera el texto completo de todos los árboles de operaciones"""
    if not arboles_operaciones:
        return "No se encontraron operaciones aritméticas en el código."
    
    resultado = ""
    for i, operacion in enumerate(arboles_operaciones, 1):
        expresion_texto = expresion_a_texto(operacion['expresion'])
        resultado += f"=== Operación {i}: {operacion['variable']} := {expresion_texto} ===\n"
        resultado += f"Árbol sintáctico:\n"
        resultado += imprimir_arbol_operacion(operacion['expresion'])
        resultado += "\n" + "="*60 + "\n\n"
    
    return resultado

# ================= INTERFAZ GRÁFICA =================
class AnalizadorGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Analizador Sintáctico PF2024 - CORREGIDO")
        self.root.geometry("1400x900")
        
        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill='both', expand=True, padx=10, pady=10)
        
        self.frame_principal = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_principal, text="Análisis Principal")
        
        self.frame_arbol = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_arbol, text="Árboles de Operaciones")
        
        self.crear_interfaz_principal()
        self.crear_interfaz_arbol()
    
    def crear_interfaz_principal(self):
        main_frame = ttk.Frame(self.frame_principal, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        ttk.Label(main_frame, text="Código fuente:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.codigo_text = scrolledtext.ScrolledText(main_frame, height=15, width=70)
        self.codigo_text.grid(row=1, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=(0, 10))
        
        # Código de ejemplo corregido
        codigo_ejemplo = '''pf2024 programa
/* Encabezado, deberá llevar el nombre del lenguaje */

decl    /* Declaración de variables */

Int a,b,c,f;
Cad d;
Bool e;

Inicio    /* Cuerpo del programa */
a:=5;
b:=3;
impcad("Dame un numero, Hola mundo");
leerdig(var);
d:=a*b-c;
d:=a+(b-c);
resultado:=a+b*c-f/2;
impcad(d);
Fin'''
        
        self.codigo_text.insert('1.0', codigo_ejemplo)
        
        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=2, column=0, columnspan=2, pady=(0, 10))
        
        ttk.Button(button_frame, text="Analizar", command=self.analizar).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="Limpiar", command=self.limpiar_todo).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="Cargar Archivo", command=self.cargar_archivo).pack(side=tk.LEFT)
        
        ttk.Label(main_frame, text="Tabla de Símbolos:").grid(row=3, column=0, sticky=tk.W, pady=(10, 5))
        
        columns = ('No.', 'Lexema', 'Token', 'Referencia')
        self.tabla_tree = ttk.Treeview(main_frame, columns=columns, show='headings', height=15)
        
        for col in columns:
            self.tabla_tree.heading(col, text=col)
            self.tabla_tree.column(col, width=150)
        
        self.tabla_tree.grid(row=4, column=0, columnspan=2, sticky=(tk.W, tk.E))
        
        scrollbar = ttk.Scrollbar(main_frame, orient=tk.VERTICAL, command=self.tabla_tree.yview)
        scrollbar.grid(row=4, column=2, sticky=(tk.N, tk.S))
        self.tabla_tree.configure(yscrollcommand=scrollbar.set)
        
        ttk.Label(main_frame, text="Mensajes:").grid(row=5, column=0, sticky=tk.W, pady=(10, 5))
        self.mensajes_text = scrolledtext.ScrolledText(main_frame, height=5, width=70)
        self.mensajes_text.grid(row=6, column=0, columnspan=2, sticky=(tk.W, tk.E))
        
        ttk.Label(main_frame, text="Errores:").grid(row=7, column=0, sticky=tk.W, pady=(10, 5))
        self.errores_text = scrolledtext.ScrolledText(main_frame, height=5, width=70)
        self.errores_text.grid(row=8, column=0, columnspan=2, sticky=(tk.W, tk.E))
        
        self.frame_principal.columnconfigure(0, weight=1)
        self.frame_principal.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(1, weight=1)
        main_frame.rowconfigure(4, weight=1)
    
    def crear_interfaz_arbol(self):
        arbol_frame = ttk.Frame(self.frame_arbol, padding="10")
        arbol_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        ttk.Label(arbol_frame, text="Árboles de Operaciones Aritméticas:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        
        self.arbol_text = scrolledtext.ScrolledText(arbol_frame, height=40, width=100, font=('Courier', 10))
        self.arbol_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        scrollbar_arbol = ttk.Scrollbar(arbol_frame, orient=tk.VERTICAL, command=self.arbol_text.yview)
        scrollbar_arbol.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.arbol_text.configure(yscrollcommand=scrollbar_arbol.set)
        
        self.frame_arbol.columnconfigure(0, weight=1)
        self.frame_arbol.rowconfigure(0, weight=1)
        arbol_frame.columnconfigure(0, weight=1)
        arbol_frame.rowconfigure(1, weight=1)
    
    def analizar(self):
        global tabla_simbolos, contador_simbolos, errores, arboles_operaciones
        
        # Reiniciar datos
        reiniciar_datos()
        
        # Limpiar interfaces
        self.mensajes_text.delete('1.0', tk.END)
        self.errores_text.delete('1.0', tk.END)
        self.arbol_text.delete('1.0', tk.END)
        
        codigo = self.codigo_text.get('1.0', tk.END)
        
        try:
            # Reiniciar lexer
            self.reiniciar_lexer()
            
            # Análisis léxico
            analizador_lexico.input(codigo)
            
            # Análisis sintáctico
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            resultado = parser.parse(lexer=analizador_lexico)
            
            # Actualizar interfaces
            self.actualizar_tabla()
            
            arboles_texto = generar_arboles_texto()
            self.arbol_text.insert('1.0', arboles_texto)
            
            # Mensajes
            self.mensajes_text.insert(tk.END, "✅ Análisis completado exitosamente.\n")
            self.mensajes_text.insert(tk.END, f"📊 Se encontraron {len(tabla_simbolos)} símbolos.\n")
            self.mensajes_text.insert(tk.END, f"🧮 Se encontraron {len(arboles_operaciones)} operaciones aritméticas.\n")
            
            # Errores
            if errores:
                self.errores_text.insert(tk.END, "❌ Errores encontrados:\n")
                self.errores_text.insert(tk.END, "="*50 + "\n")
                
                lineas_codigo = codigo.split('\n')
                
                for i, error in enumerate(errores, 1):
                    linea_num = error['line']
                    
                    self.errores_text.insert(tk.END, f"Error #{i}:\n")
                    self.errores_text.insert(tk.END, f"  📍 Línea {linea_num}: {error['type']}\n")
                    
                    if 'desc' in error:
                        self.errores_text.insert(tk.END, f"  📝 Descripción: {error['desc']}\n")
                    
                    if isinstance(linea_num, int) and 1 <= linea_num <= len(lineas_codigo):
                        contexto = lineas_codigo[linea_num - 1].strip()
                        if contexto:
                            self.errores_text.insert(tk.END, f"  📄 Código: {contexto}\n")
                    
                    self.errores_text.insert(tk.END, "-"*30 + "\n")
            else:
                self.errores_text.insert(tk.END, "✅ No se encontraron errores.")

        except Exception as e:
            self.mensajes_text.insert(tk.END, f"❌ Error durante el análisis: {str(e)}\n")
    
    def actualizar_tabla(self):
        for item in self.tabla_tree.get_children():
            self.tabla_tree.delete(item)
        
        for simbolo in tabla_simbolos:
            self.tabla_tree.insert('', 'end', values=(
                simbolo.numero,
                simbolo.lexema,
                simbolo.token,
                simbolo.referencia or ''
            ))
    
    def limpiar_todo(self):
        global tabla_simbolos, contador_simbolos, errores, arboles_operaciones
        
        reiniciar_datos()
        
        self.actualizar_tabla()
        self.mensajes_text.delete('1.0', tk.END)
        self.errores_text.delete('1.0', tk.END)
        self.arbol_text.delete('1.0', tk.END)
        
        self.mensajes_text.insert(tk.END, "🗑️ Datos limpiados.\n")
    
    def cargar_archivo(self):
        file_path = filedialog.askopenfilename(
            title="Seleccionar archivo",
            filetypes=[("Archivos de texto", "*.txt"), ("Todos los archivos", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as file:
                    contenido = file.read()
                    self.codigo_text.delete('1.0', tk.END)
                    self.codigo_text.insert('1.0', contenido)
                    self.mensajes_text.delete('1.0', tk.END)
                    self.mensajes_text.insert(tk.END, f"📁 Archivo cargado: {file_path}\n")
            except Exception as e:
                self.mensajes_text.insert(tk.END, f"❌ Error al cargar el archivo: {str(e)}\n")

    def reiniciar_lexer(self):
        """Reinicia el lexer y su contador de líneas"""
        global analizador_lexico
        analizador_lexico.lineno = 1
        analizador_lexico.lexpos = 0

# ================= EJECUCIÓN PRINCIPAL =================
if __name__ == "__main__":
    print("="*60)
    
    root = tk.Tk()
    app = AnalizadorGUI(root)
    root.mainloop()
