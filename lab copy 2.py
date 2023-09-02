"""
6.1010 Spring "23 Lab 11: LISP Interpreter Part 1
"""
#!/usr/bin/env python3

import sys
import doctest
import traceback

sys.setrecursionlimit(20_000)

# NO ADDITIONAL IMPORTS!

#############################
# Scheme-related Exceptions #
#############################


class SchemeError(Exception):
    """
    A type of exception to be raised if there is an error with a Scheme
    program.  Should never be raised directly; rather, subclasses should be
    raised.
    """

    pass


class SchemeSyntaxError(SchemeError):
    """
    Exception to be raised when trying to evaluate a malformed expression.
    """

    pass


class SchemeNameError(SchemeError):
    """
    Exception to be raised when looking up a name that has not been defined.
    """

    pass


class SchemeEvaluationError(SchemeError):
    """
    Exception to be raised if there is an error during evaluation other than a
    SchemeNameError.
    """

    pass



##############
# Frame Class #
##############


class Frame:
    """
    Objects that represent enclosing frames
    """
    def __init__(self, parent=None):
        self.assignments = {}
        self.parent = parent

    def __str__(self):
        return str(self.assignments)

    def __contains__(self, var):
        if var in self.assignments:
            return True

        elif self.parent is None:
            return False
        else:
            return var in self.parent

    def get_item(self, value):
        if value in self.assignments:
            return self.assignments[value]

        elif self.parent is not None:
            return self.parent.get_item(value)
        elif self.parent is None:
            raise SchemeNameError

    def set_item(self, var, val):
        self.assignments[var] = val


    def soft_del(self, to_del):
        
        if to_del in self.assignments:
            return self.assignments.pop(to_del)
        else:
            raise SchemeNameError

    def history(self):
        if self.parent is None:
            return ""
        else:
            out_str = str(self.assignments) + " | " + self.parent.history()
            return out_str

    def change_up(self, var, val):
        if var in self.assignments:
            self.assignments[var] = val

        elif self.parent is not None:
            self.parent.change_up(var, val)
        


class UserFunc:
    '''
    Class the represents user generated functions
    '''
    def __init__(self, arguments, frame, function):
        
        self.arguments = arguments
        self.frame = frame
        self.function = function

    def __call__(self, arguments):
        new_frame = Frame()
        new_frame.parent = self.frame

        if len(arguments) != len(self.arguments):
            # print("SchemeEvaluationError")
            raise SchemeEvaluationError

        for i, arg in enumerate(arguments):
            new_frame.assignments[self.arguments[i]] = arg
        
        return evaluate(self.function, new_frame)

    def __str__(self):
        # return f"{self.arguments}, {self.frame}, {self.function}"
        return f"{self.function}"


class Pair:
    def __init__(self, car, cdr):
        self.car = car # cur
        self.cdr = cdr # next

    def __str__(self):
        if self.cdr is None:
            return ""
        else:
            return str(self.car) + "|" + str(self.cdr.__str__())


    def is_list(self, post_list = None):
        # print(self)
        if isinstance(self, Pair) is False:
            return scheme_bools["#f"]

        if isinstance(self, Pair) is True:
            if self.cdr != Nil():
                return self.cdr.is_list(self)

        return scheme_bools["#t"]

    def get_length(self):
        length = 0
        while True:
            length += 1
            self = self.cdr
            if self == Nil():
                break
        return length

    def at_index(self, index):
        
        cur = 0
        while True:
            # print(cur, index)
            if cur == index:
                return self.car
            else:
                cur += 1
                if self ==  Nil():
                    raise SchemeEvaluationError
                self = self.cdr

    def set_value(self, index, val):

        cur = 0
        while True:

            if cur == index:
                self.car = val
                break
            else:
                cur += 1
                if self ==  Nil():
                    raise SchemeEvaluationError
                self = self.cdr        

    def copy(self):
        
        current = Pair(self.car, None)
        saved = current
        
        while True:
            self = self.cdr
            if self == Nil():
                current.cdr = Nil()
                break
            current.cdr = Pair(self.car, None)
            current = current.cdr
    
        return saved

    def pair_append(self, to_append, frame=None):
        
        self_copy = self.copy()

        next = self_copy
        saved = next
        for next_list in to_append:
            while True:
                if self_copy == Nil():
                    # self_copy.cdr = evaluate(next_list, frame).copy()
                    self_copy.cdr = next_list.copy()
                    break

                self_copy = self_copy.cdr

            self_copy = self_copy.cdr

            while True:
                if next.cdr == Nil():
                    break
                next = next.cdr
            
            next.cdr = self_copy
            next = next.cdr

        return saved 

class Nil:
    def __init__(self):
        self.name = "nil"
    
    def __str__(self):
        return "nil"
    
    def __eq__(self, other):
        if isinstance(other, Nil):
            return True
        return False


    def is_list(self, args=None):
        return scheme_bools["#t"]

    def get_length(self):
        return 0    

    def at_index(self, index):
        raise SchemeEvaluationError    

    def copy(self):
        return Nil()

    def pair_append(self, args=None, frame = None):
        new_command = ["append"]
        for arg in args:
            new_command.append(arg)
        return evaluate(new_command, frame)
      
############################
# Tokenization and Parsing #
############################


def number_or_symbol(value):
    """
    Helper function: given a string, convert it to an integer or a float if
    possible; otherwise, return the string itself

    >>> number_or_symbol("8")
    8
    >>> number_or_symbol("-5.32")
    -5.32
    >>> number_or_symbol("1.2.3.4")
    "1.2.3.4"
    >>> number_or_symbol("x")
    "x"
    """
    try:
        return int(value)
    except ValueError:
        try:
            return float(value)
        except ValueError:
            return str(value)


def handle_add(to_add, tokenized):
    if to_add != "":
        tokenized.append(to_add)
        to_add = ""

    return to_add, tokenized


def tokenize(inp_str):
    """
    Splits an input string into meaningful tokens (left parens, right parens,
    other whitespace-separated values).  Returns a list of strings.

    Arguments:
        source (str): a string containing the source code of a Scheme
                      expression

    """
    # if len(inp_str) > 1:
    #     print(inp_str)
    tokenized = []
    to_add = ""
    comment = False

    for i, char in enumerate(inp_str):
        if char == ";" or comment is True:
            comment = True
            to_add, tokenized = handle_add(to_add, tokenized)

            if char == "\n":
                comment = False

        elif char in ("(", ")"):
            to_add, tokenized = handle_add(to_add, tokenized)
            tokenized.append(char)

        elif char == "\n":
            to_add, tokenized = handle_add(to_add, tokenized)

        elif char == " " or i == len(inp_str) - 1:
            if char not in (" ", ""):
                to_add += char

            to_add, tokenized = handle_add(to_add, tokenized)

        else:
            to_add += char

    return tokenized


def eval_token(token):
    try:
        float(token)
        if float(token) == int(float(token)):
            return int(token)
        else:
            return float(token)
    except:
        str(token)
        return str(token)


def parse(tokens):
    """
    Parses a list of tokens, constructing a representation where:
        * symbols are represented as Python strings
        * numbers are represented as Python ints or floats
        * S-expressions are represented as Python lists

    Arguments:
        tokens (list): a list of strings representing tokens
    """
    keywords = {
        "declare",
        "make-environment",
        "define",
        "delay",
        "unassigned?",
        "default-object?",
        "or",
        "in-package",
        "lambda",
        "using-syntax",
        "and",
        "cond",
        "letrec",
        "access",
        "named-lambda",
        "define-integrable",
        "quote",
        "sequence",
        "define-syntax",
        "bkpt",
        "quasiquote",
        "if",
        "scode-quote",
        "let-syntax",
        "cons-stream",
        "case",
        "do",
        "let*",
        "macro",
        "local-declare",
        "the-environment",
        "let",
        "set!",
        "define-macro",
        "begin",
        "flu-let",
    }

    if (
        (tokens[0] == "(" and tokens[-1] != ")")
        or tokens[0] == ")"
        or tokens[-1] == "("
    ):
        raise SchemeSyntaxError

    brac_count = {"(": 0, ")": 0}

    for i, token in enumerate(tokens):
        if token in {"(", ")"}:
            brac_count[token] += 1
        if token in keywords and tokens[i - 1] != "(":
            raise SchemeSyntaxError

    if brac_count["("] != brac_count[")"]:
        raise SchemeSyntaxError

    def convert_list(toks):
        stack = []
        result = []
        for token in toks:
            if token == "(":
                stack.append(result)
                result = []
            elif token == ")":
                temp = result
                result = stack.pop()
                result.append(temp)
            else:
                token = eval_token(token)
                result.append(token)
        return result

    # print(tokens)
    result = convert_list(tokens)[0]
    
    # if len(result) > 1:
    #     return convert_list(tokens)

    return result


######################
# Built-in Functions #
######################


def equal(numbers):
    '''
    tests if a list follows ==
    '''
    for i in range(len(numbers) - 1):
        if numbers[i] != numbers[i+1]:
            return False
    return True

def geq(numbers):
    '''
    tests if a list follows >=
    '''
    for i in range(len(numbers) - 1):
        if numbers[i] < numbers[i+1]:
            return False
    return True

def greaterthan(numbers):
    '''
    tests if a list follows >
    '''
    for i in range(len(numbers) - 1):
        if numbers[i] <= numbers[i+1]:
            return False
    return True

def leq(numbers):
    '''
    tests if a list follows <=
    '''
    for i in range(len(numbers) - 1):
        if numbers[i] > numbers[i+1]:
            return False
    return True

def lessthan(numbers):
    '''
    tests if a list follows <
    '''
    for i in range(len(numbers) - 1):
        if numbers[i] >= numbers[i+1]:
            return False
    return True


def product(factors):
    """
    Computes the product of a list
    """
    out = 1
    for val in factors:
        out *= val
    return out

def divide(dividends):
    """
    Divides every element in a list by the next element
    """
    if len(dividends) == 1:
        raise SchemeError

    ini = dividends[0]
    for val in dividends[1:]:
        ini /= val
    return ini

def if_logic(tree, frame):
    """
    handles the logic for if-statements
    """
    if evaluate(tree[1], frame):
        return evaluate(tree[2], frame)
    else:
        return evaluate(tree[3], frame)

def andor_logic(tree, frame, boolean):
    '''
    handles the logic for both and and or
    '''
    
    try_andor = []
    for exp in tree[1:]:
        try_andor.append( evaluate(exp, frame) )
        if try_andor[-1] is boolean:
            return boolean

    return not boolean

def not_logic(args):
    if len(args) != 1:
        raise SchemeEvaluationError
    else:
        return not args[0]


def cons(args):
    if len(args) != 2:
        raise SchemeEvaluationError
    new_pair = Pair(args[0], args[1])
    return new_pair

def car(args):
    if len(args) != 1:
        raise SchemeEvaluationError
    if isinstance(args[0], Pair) is False:
        raise SchemeEvaluationError
    return args[0].car

def cdr(args):
    if len(args) != 1:
        raise SchemeEvaluationError
    if isinstance(args[0], Pair) is False:
        raise SchemeEvaluationError
    return args[0].cdr

def create_list(args):
    if len(args) == 0:
        return Nil()
    if len(args) == 1:
        return Pair(args[0], Nil())
    else:
        return Pair(args[0], create_list(args[1:]))



def list_question(args):
    try:
        # print(args[0].is_list())
        return args[0].is_list()
    except:
        return False
        
def length(args):
    if len(args) > 1:
        raise SchemeEvaluationError
    try:
        args[0].is_list()
    except:
        raise SchemeEvaluationError

    return args[0].get_length()

def listref(args):
    arg_list = args[0]
    arg_ind = args[1]
    
    try:
        arg_list.is_list()
        return arg_list.at_index(arg_ind)
    except:
        if isinstance(arg_list, Pair):
            if arg_ind != 0:
                raise SchemeEvaluationError
            return arg_list.car
        else:
            raise SchemeEvaluationError

def append_func(args):
    for pos_list in args:
        try:
            pos_list.is_list()
        except:
            raise SchemeEvaluationError
    if len(args) == 0:
        return Nil()
    elif len(args) == 1:
        return args[0].copy()
    else:
        return args[0].pair_append(args[1:])



def map_func(args):
    func = args[0]
    to_apply_list = args[1]
    try:
        to_apply_list.is_list()
    except:
        raise SchemeEvaluationError

    ini_length = to_apply_list.get_length()
    copied_list = to_apply_list.copy()
    for i in range(ini_length):
        cur = to_apply_list.at_index(i)
        mapped = func([cur])
        copied_list.set_value(i, mapped)

    return copied_list

def filter_func(args):
    
    func = args[0]
    to_apply_list = args[1]
    try:
        to_apply_list.is_list()
    except:
        raise SchemeEvaluationError

    ini_length = to_apply_list.get_length()
    first = Nil()
    saved = first
    for i in range(ini_length):
        cur = to_apply_list.at_index(i)
        filtered = func([cur])
        if filtered is True:
            if first == Nil():
                first = Pair(cur, Nil())
                saved = first
            else:
                next = Pair(cur, Nil())
                first.cdr = next
                first = first.cdr

    return saved

def reduce(args):
    func = args[0]
    to_apply_list = args[1]
    initial = args[2]
    try:
        to_apply_list.is_list()
    except:
        raise SchemeEvaluationError

    ini_length = to_apply_list.get_length()
    final = initial
    for i in range(ini_length):
        cur = to_apply_list.at_index(i)
        final = func([final, cur])
    return final



def begin(tree, frame):
    for i, arg in enumerate(tree[1:]):
        if i == len(tree) - 2:
            return evaluate(arg, frame)
        evaluate(arg, frame)

def del_func(tree, frame):
    return frame.soft_del(tree[1])

def let(tree, frame):
    new_frame = Frame()
    new_frame.parent = frame

    var_vals = tree[1]

    for vv_pair in var_vals:
        val = evaluate(vv_pair[1], frame)   
        new_frame.set_item(vv_pair[0], val)

    return evaluate(tree[2], new_frame)

def setbang(tree, frame):
    val_update = evaluate(tree[2], frame)
    var_update = tree[1] #evaluate(tree[1], frame)

    if var_update in frame:
        
        frame.change_up(var_update, val_update)
    else:
        raise SchemeNameError

    return val_update


scheme_builtins = {
    "+": sum,
    "-": lambda args: -args[0] if len(args) == 1 else (args[0] - sum(args[1:])),
    "*": product,
    "/": divide,
    "equal?": equal,
    ">":greaterthan,
    "<": lessthan,
    ">=":geq,
    "<=":leq,

    "cons":cons,
    "car":car,
    "cdr":cdr,
    "list":create_list,
    
 
    "length":length,
    "list-ref":listref,
    "append":append_func,
    "map":map_func,
    "filter":filter_func,
    "reduce":reduce,
    "list?":list_question,
    "not":not_logic,
    

}

new_specforms = {
   
    # define x length
    # "x ": length
    "del":del_func,
    "set!":setbang,
    "let":let,
    "begin":begin,

    "if":if_logic,
    "and":andor_logic,
    "or":andor_logic,

}


scheme_bools = {
    "#t":True,
    "#f":False,
}



builtins = Frame()
builtins.assignments = scheme_builtins

def create_builtingframe():
    builtins = Frame()
    builtins.assignments = scheme_builtins
    return builtins



##############
# Evaluation #
##############

def convert_to_cons(tree):
    '''
    converts a list argument to a cons expression
    '''
    if len(tree) == 1:
        return "nil"

    if len(tree) == 2:
        return ["cons", tree[1], "nil"]

    else:
        # print(["cons", tree[1], evaluate(tree[2], frame)])
        new_exp = ["list"] + tree[2:]
        # print(evaluate(new_exp, frame))
        return ["cons", tree[1], convert_to_cons(new_exp)]


def reduce_helper(tree, frame):
    '''
    handles the reduce function
    '''
    function = tree[1]

    inital = tree[3]


    pair_expression = evaluate(tree[2], frame)
    exp_length = pair_expression.get_length()
    # copied_exp = pair_expression.copy()    

    final = inital

    for i in range(exp_length):
        cur_num = pair_expression.at_index(i) 
        
        # print(function, evaluate(final, frame), cur_num)
        final = evaluate([function, evaluate(final, frame), cur_num], frame)      
        # print(final)  
        
    return final


def handle_strings(tree, frame):
    '''
    Handles the case where the input tree is a string
    '''

    if tree == "nil":
        return Nil()

    if str(tree) in scheme_bools:
        return scheme_bools[str(tree)]

    var_val = frame.get_item(str(tree))    

    return var_val


def refactor_input(tree, frame):
    """
    Refractors input with simplified lambda calls
    """
    arg_len = len(tree[1]) - 1
       
    if arg_len > 0:
        new_inp = [
            tree[0],
            tree[1][0],
            ["lambda", tree[1][1:], tree[2]],
        ]
    else:
        new_inp = [tree[0], tree[1][0], ["lambda", [], tree[2]]]
    return evaluate(new_inp, frame)


def operate(operator, operands, frame=None):
    '''
    Computes the output ofa builtin method
    '''
    
    if frame is not None:
        for i, operand in enumerate(operands):
            if operand in frame:
                # print(operand)
                
                operands[i] = frame.get_item(operand)

            elif isinstance(operand, str):
                raise SchemeNameError


    return scheme_builtins[operator](operands)


def evaluate(tree, frame=None):
    '''
    Evaluates a given inputted line, based on previous lines
    '''
    # print(tree)
    # print()
    
    if frame is None:
        frame = Frame()
        frame.parent = create_builtingframe()

    match tree:
        case float(tree) | int(tree):
            return tree

        case str(tree):
            # print(tree, type(frame))
            return handle_strings(tree, frame)

        case Nil():
            return Nil()

        case Pair():
            return tree

        case list(tree):
            if len(tree) == 0:                
                raise SchemeEvaluationError

            # if tree[0] == "fizzbuzz":
            #     raise SchemeNameError

            if tree[0] == "HISTORY":
                return frame.history()
            
            if tree[0] == "define" and len(tree) == 3:
                
                if isinstance(tree[1], str):
                    defined_val = evaluate(tree[2], frame)
                    frame.set_item(tree[1], defined_val)
                    return defined_val
               
                if isinstance(tree[1], list):
                    
                    return refactor_input(tree, frame)
                    
                else:
                    raise SchemeSyntaxError

            if tree[0] == "lambda":  
                arguments = tree[1]
                function = tree[2]
                defined_func = UserFunc(arguments, frame, function)
                return defined_func
        
            
            if tree[0] == "if":
                return if_logic(tree, frame)

            elif tree[0] == "and":
                return andor_logic(tree, frame, False)

            elif tree[0] == "or":
                return andor_logic(tree, frame, True)



            if tree[0] == "begin":
                return begin(tree, frame)
            
            if tree[0] == "del":
                return del_func(tree, frame)

            if tree[0] == "let":
                return let(tree, frame)
            
            if tree[0] == "set!":
                return setbang(tree, frame)

            new_tree = []
            
            for val in tree: 
                # print(val)
                new_tree.append(evaluate(val, frame) )
            tree = new_tree
            
            function = tree[0]
            if not callable(function):
                raise SchemeEvaluationError
            return function(tree[1:])



counter = [0]
def result_and_frame(tree, frame=None):
    '''
    Allows for the storing of multiple lines of inputs
    '''
    print()
    print(f"{counter[0]} INPUT:", tree)
    counter[0] += 1
    if frame is None:
        frame = Frame()
        frame.parent = create_builtingframe()

    return (evaluate(tree, frame), frame)


def evaluate_file(file_name, frame=None):
    
    file = open(file_name, mode="r") 
    tokenized_file = tokenize(file.read())
    parsed_file = parse(tokenized_file)

    return evaluate(parsed_file, frame)

def repl(verbose=False, frame=None):
    """
    Read in a single line of user input, evaluate the expression, and print
    out the result. Repeat until user inputs "QUIT"

    Arguments:
        verbose: optional argument, if True will display tokens and parsed
            expression in addition to more detailed error output.
    """
    # import traceback
    

    _, frame = result_and_frame(["+"], frame)  # make a global frame
    while True:
        input_str = input("in> ")
        if input_str == "QUIT":
            return
        try:
            token_list = tokenize(input_str)
            if verbose:
                print("tokens>", token_list)
            expression = parse(token_list)
            if verbose:
                print("expression>", expression)
            output, frame = result_and_frame(expression, frame)
            print("  out>", output)
        except SchemeError as e:
            if verbose:
                traceback.print_tb(e.__traceback__)
            print("Error>", repr(e))


