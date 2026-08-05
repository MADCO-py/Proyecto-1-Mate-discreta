import re
import sys
import itertools

# ---------------------------------------------------------------
# Estado global del programa
# ---------------------------------------------------------------
conjuntos = {}          # nombre (str) -> frozenset de elementos
referencial = None      # nombre (str) del conjunto referencial/universo


# ---------------------------------------------------------------
# Utilidades de parseo de conjuntos y elementos
# ---------------------------------------------------------------
def split_top_level(s, sep=','):
    """Divide 's' por 'sep', pero ignora separadores dentro de parentesis
    (para poder reconocer pares ordenados como (1,a) como un solo elemento)."""
    partes = []
    profundidad = 0
    actual = ''
    for ch in s:
        if ch == '(':
            profundidad += 1
            actual += ch
        elif ch == ')':
            profundidad -= 1
            actual += ch
        elif ch == sep and profundidad == 0:
            partes.append(actual)
            actual = ''
        else:
            actual += ch
    partes.append(actual)
    return partes


def normaliza_atomo(token):
    """Convierte un token a int si es numerico, si no lo deja como str."""
    token = token.strip()
    if re.fullmatch(r'-?\d+', token):
        return int(token)
    return token


def parse_elemento(token):
    token = token.strip()
    if token.startswith('(') and token.endswith(')'):
        interior = token[1:-1]
        partes = split_top_level(interior, ',')
        return tuple(normaliza_atomo(p) for p in partes)
    return normaliza_atomo(token)


def parse_conjunto_literal(texto):
    """Convierte una cadena '{a,b,c}' o '{(1,a),(2,b)}' en un frozenset."""
    texto = texto.strip()
    if not (texto.startswith('{') and texto.endswith('}')):
        raise ValueError('Un conjunto debe escribirse entre llaves, por ejemplo {a,b,c}')
    interior = texto[1:-1].strip()
    if interior == '':
        return frozenset()
    tokens = split_top_level(interior, ',')
    return frozenset(parse_elemento(t) for t in tokens if t.strip() != '')


def formatea_elemento(e):
    if isinstance(e, tuple):
        return '(' + ', '.join(formatea_elemento(x) for x in e) + ')'
    return str(e)


def formatea_conjunto(s):
    if len(s) == 0:
        return '{}'
    elementos = sorted(s, key=lambda x: formatea_elemento(x))
    return '{' + ', '.join(formatea_elemento(e) for e in elementos) + '}'


# ---------------------------------------------------------------
# Traduccion de sintaxis LaTeX a la sintaxis simple del parser
#   \cup      -> +
#   \cap      -> *
#   \times    -> x
#   \setminus -> \        (tambien \backslash)
#   \overline{X} -> (X)'
# ---------------------------------------------------------------
def expande_overline(s):
    out = ''
    i, n = 0, len(s)
    while i < n:
        if s[i:i + 10] == '\\overline{':
            profundidad = 1
            j = i + 10
            inicio = j
            while j < n and profundidad > 0:
                if s[j] == '{':
                    profundidad += 1
                elif s[j] == '}':
                    profundidad -= 1
                j += 1
            interior = s[inicio:j - 1]
            interior = expande_overline(interior)   # por si hay anidamiento
            out += '(' + interior + ")'"
            i = j
        else:
            out += s[i]
            i += 1
    return out


def prepara_expresion(cruda):
    """Limpia una entrada (con o sin el prefijo 'LaTeX:', y con o sin
    comandos LaTeX) y la deja lista para el tokenizador. Quitar la marca
    'LaTeX:' y traducir los comandos es seguro incluso si el texto no
    trae LaTeX, porque las sustituciones no afectan al texto simple."""
    s = cruda.strip()
    s = re.sub(r'(?i)latex:', '', s)         # quita la marca 'LaTeX:' donde aparezca
    s = expande_overline(s)                  # \overline{X}  ->  (X)'
    s = s.replace('\\cup', '+')
    s = s.replace('\\cap', '*')
    s = s.replace('\\times', 'x')
    s = s.replace('\\setminus', '\\')
    s = s.replace('\\backslash', '\\')
    s = s.replace(' ', '')
    return s


# ---------------------------------------------------------------
# Tokenizador y parser de expresiones de conjuntos
#
# Precedencia (de mayor a menor):
#   1. complemento          A'          (postfijo)
#   2. producto cartesiano  A x B
#   3. interseccion         A * B
#   4. union y diferencia   A + B , A \ B   (misma precedencia, izq->der)
#   Los parentesis ( ) agrupan y rompen la precedencia normal.
# ---------------------------------------------------------------
class Token:
    def __init__(self, kind, value=None):
        self.kind = kind
        self.value = value


def tokeniza(expr):
    tokens = []
    i, n = 0, len(expr)
    while i < n:
        c = expr[i]
        if c.isspace():
            i += 1
            continue
        if c.isupper():
            j = i
            while j < n and (expr[j].isupper() or expr[j].isdigit()):
                j += 1
            tokens.append(Token('NAME', expr[i:j]))
            i = j
            continue
        if c == 'x':
            tokens.append(Token('CART')); i += 1; continue
        if c == '+':
            tokens.append(Token('UNION')); i += 1; continue
        if c == '*':
            tokens.append(Token('INTER')); i += 1; continue
        if c == '\\':
            tokens.append(Token('DIFF')); i += 1; continue
        if c == "'":
            tokens.append(Token('COMP')); i += 1; continue
        if c == '(':
            tokens.append(Token('LP')); i += 1; continue
        if c == ')':
            tokens.append(Token('RP')); i += 1; continue
        raise ValueError(f'Caracter inesperado en la expresion: {c!r}')
    return tokens


class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def advance(self):
        tok = self.peek()
        self.pos += 1
        return tok

    def parse(self):
        val = self.parse_expr()
        if self.peek() is not None:
            raise ValueError('Sobran simbolos al final de la expresion')
        return val

    def parse_expr(self):
        izq = self.parse_term()
        while self.peek() and self.peek().kind in ('UNION', 'DIFF'):
            op = self.advance().kind
            der = self.parse_term()
            izq = (izq | der) if op == 'UNION' else (izq - der)
        return izq

    def parse_term(self):
        izq = self.parse_factor()
        while self.peek() and self.peek().kind == 'INTER':
            self.advance()
            der = self.parse_factor()
            izq = izq & der
        return izq

    def parse_factor(self):
        izq = self.parse_unary()
        while self.peek() and self.peek().kind == 'CART':
            self.advance()
            der = self.parse_unary()
            izq = frozenset(itertools.product(izq, der))   # producto cartesiano
        return izq

    def parse_unary(self):
        val = self.parse_primary()
        while self.peek() and self.peek().kind == 'COMP':
            self.advance()
            if referencial is None:
                raise ValueError('No se ha definido el conjunto referencial (universo)')
            U = conjuntos[referencial]
            val = U - val
        return val

    def parse_primary(self):
        tok = self.peek()
        if tok is None:
            raise ValueError('Expresion incompleta')
        if tok.kind == 'NAME':
            self.advance()
            if tok.value not in conjuntos:
                raise ValueError(f'El conjunto "{tok.value}" no esta definido')
            return conjuntos[tok.value]
        if tok.kind == 'LP':
            self.advance()
            val = self.parse_expr()
            if not (self.peek() and self.peek().kind == 'RP'):
                raise ValueError('Falta el parentesis de cierre')
            self.advance()
            return val
        raise ValueError(f'Token inesperado: {tok.kind}')


def evalua_expresion(texto_simple):
    tokens = tokeniza(texto_simple)
    return Parser(tokens).parse()


# ---------------------------------------------------------------
# Verificacion de funcion: fun(E)
# ---------------------------------------------------------------
def verifica_funcion(pares, nombre_dominio=None):
    if not all(isinstance(p, tuple) and len(p) == 2 for p in pares):
        print('El conjunto no esta formado unicamente por pares ordenados;')
        print('no se puede verificar si es una funcion.')
        return

    mapeo = {}
    conflictos = []
    for (a, b) in pares:
        if a in mapeo and mapeo[a] != b:
            conflictos.append((a, mapeo[a], b))
        else:
            mapeo[a] = b

    if conflictos:
        print('Resultado: NO es funcion.')
        print('Motivo: un mismo elemento del dominio se relaciona con mas de un elemento distinto:')
        for a, b1, b2 in conflictos:
            print(f'   {formatea_elemento(a)} -> {formatea_elemento(b1)}   y   '
                  f'{formatea_elemento(a)} -> {formatea_elemento(b2)}')
        return

    print('La relacion esta bien definida: cada elemento del dominio se')
    print('relaciona con un unico elemento del codominio.')

    if nombre_dominio:
        if nombre_dominio not in conjuntos:
            print(f'Aviso: el conjunto dominio "{nombre_dominio}" no esta definido;')
            print('no se pudo verificar si la funcion es total.')
            print('Resultado: Es funcion (bien definida).')
            return
        dominio = conjuntos[nombre_dominio]
        primeros = set(mapeo.keys())
        faltantes = dominio - primeros
        if faltantes:
            print(f'Faltan elementos de {nombre_dominio} sin imagen asignada: '
                  f'{formatea_conjunto(frozenset(faltantes))}')
            print('Resultado: NO es funcion total (esta bien definida, pero no cubre todo el dominio).')
        else:
            print(f'Todos los elementos de {nombre_dominio} tienen imagen asignada.')
            print('Resultado: SI es funcion (funcion total).')
    else:
        print('Resultado: SI es funcion (bien definida; no se especifico un conjunto dominio '
              'para verificar totalidad).')


# ---------------------------------------------------------------
# Procesamiento de una linea de "operacion"
# ---------------------------------------------------------------
def procesa_operacion(cruda, interactivo=True):
    preparado = prepara_expresion(cruda)

    m = re.match(r'^fun\((.*)\)$', preparado, re.IGNORECASE | re.DOTALL)
    if m:
        partes = split_top_level(m.group(1), ',')     # fun(EXPR) o fun(EXPR,DOMINIO)
        resultado = evalua_expresion(partes[0])
        print(f'Conjunto evaluado dentro de fun(...): {formatea_conjunto(resultado)}')
        dominio = partes[1].strip() if len(partes) > 1 and partes[1].strip() else None
        if dominio is None and interactivo:
            dominio = input(
                'Nombre del conjunto dominio para verificar si es funcion TOTAL '
                '(Enter para omitir): ').strip() or None
        verifica_funcion(resultado, dominio)
        return

    resultado = evalua_expresion(preparado)
    print(f'Resultado: {formatea_conjunto(resultado)}')


# ---------------------------------------------------------------
# Carga por lotes desde un archivo .txt
#
# Formato esperado (los encabezados "Conjuntos:" y "Operaciones:" son
# opcionales, solo se ignoran si aparecen):
#
#   Conjuntos:
#   U:={a,b,c,d,e,f,g,h,i,j,k,1,2,3,4,5}
#   A:={a,1,3,d,g,h,4,5}
#   ...
#   Operaciones:
#   A \cup C
#   A\B
#   fun(E)
#   fun(A \times B, A)      <- domino opcional como 2do argumento
# ---------------------------------------------------------------
def procesa_archivo(ruta):
    global referencial
    try:
        with open(ruta, encoding='utf-8') as f:
            lineas = f.readlines()
    except OSError as e:
        print(f'No se pudo abrir el archivo: {e}')
        return

    print(f'--- Cargando archivo: {ruta} ---')
    for cruda in lineas:
        linea = cruda.strip()
        if not linea or linea.lower() in ('conjuntos:', 'operaciones:'):
            continue

        m = re.match(r'^([A-Za-z][A-Za-z0-9]*)\s*:=\s*(.+)$', linea)
        if m:
            nombre, literal = m.group(1), m.group(2)
            try:
                conjuntos[nombre] = parse_conjunto_literal(literal)
                print(f'{nombre} = {formatea_conjunto(conjuntos[nombre])}')
                if nombre.upper() == 'U' and referencial is None:
                    referencial = nombre
                    print(f'  ("{nombre}" se toma automaticamente como conjunto referencial)')
            except ValueError as e:
                print(f'ERROR al definir {nombre}: {e}')
            continue

        print(f'>> {linea}')
        try:
            procesa_operacion(linea, interactivo=False)
        except ValueError as e:
            print(f'ERROR: {e}')

    print('--- Fin del archivo ---')


# ---------------------------------------------------------------
# Menu interactivo
# ---------------------------------------------------------------
def menu():
    print('=' * 60)
    print(' PROGRAMA DE TEORIA DE CONJUNTOS Y FUNCIONES')
    print('=' * 60)
    print('Simbolos disponibles para escribir operaciones:')
    print("   +   union                A+B")
    print("   *   interseccion         A*B")
    print("   \\   diferencia           A\\B")
    print("   '   complemento          A'")
    print("   x   producto cartesiano  AxB")
    print("   ( ) simbolos de agrupacion")
    print('   fun(EXPR)  o  fun(EXPR,DOMINIO)   verifica si EXPR es una funcion')
    print('   Tambien se acepta el prefijo "LaTeX:" usando \\cup \\cap \\times \\overline{} \\setminus')
    print()

    if len(sys.argv) > 1:
        procesa_archivo(sys.argv[1])

    while True:
        print('-' * 60)
        print('1) Definir un conjunto')
        print('2) Definir el conjunto referencial (universo)')
        print('3) Evaluar una operacion / expresion')
        print('4) Cargar conjuntos y operaciones desde un archivo .txt')
        print('5) Listar conjuntos definidos')
        print('6) Salir')
        opcion = input('Elige una opcion: ').strip()

        global referencial
        try:
            if opcion == '1':
                nombre = input('Nombre del conjunto (por ejemplo A): ').strip()
                literal = input(f'{nombre} := ').strip()
                conjuntos[nombre] = parse_conjunto_literal(literal)
                print(f'{nombre} = {formatea_conjunto(conjuntos[nombre])}')

            elif opcion == '2':
                nombre = input('Nombre del conjunto referencial (por ejemplo U): ').strip()
                literal = input(f'{nombre} := ').strip()
                conjuntos[nombre] = parse_conjunto_literal(literal)
                referencial = nombre
                print(f'Conjunto referencial definido: {nombre} = {formatea_conjunto(conjuntos[nombre])}')

            elif opcion == '3':
                expr = input('Escribe la operacion (o "LaTeX: ..."): ').strip()
                procesa_operacion(expr, interactivo=True)

            elif opcion == '4':
                ruta = input('Ruta del archivo .txt: ').strip()
                procesa_archivo(ruta)

            elif opcion == '5':
                if not conjuntos:
                    print('Aun no hay conjuntos definidos.')
                else:
                    for nombre, s in conjuntos.items():
                        marca = '  (referencial)' if nombre == referencial else ''
                        print(f'{nombre} = {formatea_conjunto(s)}{marca}')

            elif opcion == '6':
                print('Fin del programa.')
                break

            else:
                print('Opcion invalida.')

        except ValueError as e:
            print(f'ERROR: {e}')


if __name__ == '__main__':
    try:
        menu()
    except (EOFError, KeyboardInterrupt):
        print('\nFin del programa.')