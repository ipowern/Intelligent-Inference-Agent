import re, sys, copy, ast
operators_list = ['&&', '=>']
std_variable_counter = 0
unified_sol = {}
goals_book = set()

'''Setting Environment'''

def parse_stmt(sen):
    sen = '(' + sen + ')'
    sen = sen.replace('(', ' ( ')
    sen = sen.replace(')', ' ) ')
    sen = sen.replace(',', ' ')
    tokens = sen.split()
    return fixstmt(tokens)

def fixstmt(List):
    first = List.pop(0)
    if first == '(':
        newSentence = []
        while List[0] != ')':
            recheck = fixstmt(List)
            newSentence.append(recheck)
        List.pop(0)
        return newSentence
    else:
        return first

'''Compound Expressions'''

def isPredicate(expr):
    res1 = expr.op in operators_list
    res2 = expr.op[0].isupper()
    res3 = not res1 and res2
    return res3

def isVariable(unit):
    if not isinstance(unit, Compound):
        return False
    else:
        res1 = unit.op.islower()
        res2 = unit.args == []
        res3 = res1 and res2
        return isinstance(unit, Compound) and res3

def makeCompound(unit):

    if isinstance(unit, Compound):
        res_stmt = unit
        return res_stmt

    if '=>' in unit:
        pos = unit.index('=>')
        rhs = unit[pos + 1:]
        lhs = unit[:pos]
        implargs = [lhs, rhs]
        res_stmt = Compound('=>', implargs)
        return res_stmt

    elif '&&' in unit:
        pos = unit.index('&&')
        second = unit[pos + 1:]
        first = unit[:pos]
        amprargs = [first, second]
        res_stmt = Compound('&&', amprargs)
        return res_stmt

    elif isinstance(unit, str):
        res_stmt = Compound(unit)
        return res_stmt

    if len(unit) == 1:
        return makeCompound(unit[0])

    return Compound(unit[0], unit[1:][0])

class Compound:
    def __init__(self, op, args = []):
        self.op = op
        self.args = map(makeCompound, args)

    def __eq__(self, other):
        res1 = isinstance(other, Compound)
        if res1:
            res2 = self.op == other.op
            res3 = self.args == other.args
            res4 = res2 and res3
            return res1 and res4
        else:
            return False

    def __hash__(self):
        collect_args = tuple(self.args)
        hash_operator = hash(self.op)
        hash_args = hash(collect_args)
        hash_res = hash_operator * hash_args
        return hash_res

    def __repr__(self):
        if len(self.args) == 0:
            return self.op

        elif self.op not in operators_list:
            args = str(self.args[0])
            for arg in self.args[1:]:
                args = args + ', ' + str(arg)
            return self.op + '(' + args + ')'

        else:
            compound = ''
            if self.args[0].op in operators_list:
                args_to_str = str(self.args[0])
                compound = '(' + args_to_str + ')'
            else:
                args_to_str = str(self.args[0])
                compound = args_to_str
            compound = compound + ' ' + self.op + ' '

            if self.args[1].op in operators_list:
                args_to_str = str(self.args[1])
                compound = compound + '(' + args_to_str + ')'
            else:
                args_to_str = str(self.args[1])
                compound = compound + args_to_str
            return compound


'''KB tell,ask algo'''

class KnowledgeBase:
    def __init__(self, initial_exprs = []):
        self.exprs = {}
        for expr in initial_exprs:
            self.tell(expr)

    def getPredicate(self, goal):
        if not isPredicate(goal):
            return self.getPredicate(goal.args[0])
        else:
            return goal.op

    def prepKb(self, finalstmt, tempstmt):
        if not isPredicate(tempstmt):
            self.prepKb(finalstmt, tempstmt.args[0])
            self.prepKb(finalstmt, tempstmt.args[1])

        else:
            if tempstmt.op not in self.exprs:
                self.exprs[tempstmt.op] = [finalstmt]
            else:
                if finalstmt not in self.exprs[tempstmt.op]:
                    self.exprs[tempstmt.op].append(finalstmt)

    def tell(self, expr):
        self.prepKb(expr, expr)

    def ask(self, query):
        #print "ASK:",query
        return FOL_BC_ask(self, query)

    def fetchRulesForGoal(self, goal):
        try:
            predicate = self.getPredicate(goal)
            if predicate not in self.exprs:
                pass
            else:
                exprsforpredicate = self.exprs[predicate]
                return exprsforpredicate

        except IndexError:
            actexprs = []
            key = 0
            while key in self.exprs.keys():
                actexprs.append(self.exprs[key])
                key = key + 1
            set_actexprs = set(actexprs)
            return list(set_actexprs)

'''Unification algo'''

def Unify(x, y, theta = {}):
    if theta is None:
        return None
    elif x == y:
        return theta
    elif isVariable(x):
        return Unify_Var(x, y, theta)
    elif isVariable(y):
        return Unify_Var(y, x, theta)
    elif isinstance(x, Compound) and isinstance(y, Compound):
        return Unify(x.args, y.args, Unify(x.op, y.op, theta))
    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        return Unify(x[1:], y[1:], Unify(x[0], y[0], theta))
    else:
        return None

def Unify_Var(var, x, theta):
    if var in theta:
        return Unify(theta[var], x, theta)
    updated_theta = copy.deepcopy(theta)
    updated_theta[var] = x
    return updated_theta

'''Standardize Variables function'''

def genVar(stmt, vars):
            for arg in stmt.args:
                yield Standardize_Variables(arg, vars)

def Standardize_Variables(expr, standardize_variables = None):
    global std_variable_counter
    if standardize_variables is None:
        standardize_variables = {}
    if not isinstance(expr, Compound):
        return expr
    if not isVariable(expr):
        return Compound(expr.op, (genVar(expr,standardize_variables)))
    else:
        if expr not in standardize_variables:
            gen_next_var = Compound('z_' + str(std_variable_counter))
            standardize_variables[expr] = Compound('z_' + str(std_variable_counter))
            std_variable_counter = std_variable_counter + 1
            return gen_next_var
        else:
            return standardize_variables[expr]

'''Substitution function'''

def v_conversion(v_dict,v_line):

    v_dict = v_dict.replace('{','{\'')
    v_dict = v_dict.replace(': ','\':\'')
    v_dict = v_dict.replace(', ','\',\'')
    v_dict = v_dict.replace('}','\'}')

    if v_dict != "{''}":
        #print "ENTERED"
        temp_dict = ast.literal_eval(v_dict)
        for key in temp_dict:
            v_line = re.sub(r'\b{0}\b'.format(re.escape(key)), temp_dict[key], v_line)
        v_line = re.sub(r'z_\w*', '_', v_line)
        v_line = re.sub(r'\s[a-z]', ' _', v_line)
        v_line = re.sub(r'[(][a-z]', '(_', v_line)
        return v_line
    else:
        v_line = re.sub(r'\s[a-z]', ' _', v_line)
        v_line = re.sub(r'[(][a-z]', '(_', v_line)
        return v_line

def compare_args(one,two):
    for i in two:
        for arg in i.args:
            if not isVariable(arg) and arg not in one.args:
                return False
    return True

def space(expr):
    if expr.op not in ['&&']:
        pass
    else:
        args = [space(expr.args[0]), space(expr.args[1])]
        expr = Compound(expr.op, args)
    return expr

def lhs_and_rhs(expr):
    if expr.op != '=>':
        lhs = []
        rhs = expr
    else:
        lhs = space(expr.args[0])
        rhs = expr.args[1]
    return lhs,rhs

def substitute(theta, expr):
    if not isVariable(expr):
        res_expr = Compound(expr.op, (genVar(expr,theta)))
    else:
        if expr in theta:
            res_expr = theta[expr]
        else:
            res_expr = expr
    return res_expr

'''First Order Logic Backward Chaining Algorithm Implementation'''

def FOL_BC_ask(KB, query):
    return FOL_BC_or(KB, query, {})

def FOL_BC_or(KB, goal, theta):
    global unified_sol
    '''if goal in goals_book:
        print "Ask:",v_conversion(str(theta),goal.__repr__())
        return
    goals_book.add(goal)'''
    flag1 = False
    #print unified_sol
    #print goal
    print "Ask:",v_conversion(str(theta),goal.__repr__())
    #print
    fetched_rules_for_goal = KB.fetchRulesForGoal(goal)
    if len(fetched_rules_for_goal) != 0:
        flag2 = True
        for rule in fetched_rules_for_goal:
            stdRule = Standardize_Variables(rule)
            lhs, rhs = lhs_and_rhs(stdRule)
            unify_sol = Unify(rhs, goal, theta)
            unified_sol = unify_sol
            if unify_sol == None:
                continue
            if flag2 == False:
                #print unified_sol
                #print goal
                print "Ask:",v_conversion(str(theta),goal.__repr__())
                #print
            for theta1 in FOL_BC_and(KB, lhs, unify_sol):
                #print unified_sol
                #print goal
                flag1 = True
                print "True:",v_conversion(str(theta1),goal.__repr__())
                '''if goal in goals_book:
                    flag1 = True
                    print "True:",v_conversion(str(theta1),goal.__repr__())
                    goals_book.remove(goal)'''
                #print
                yield theta1
            flag2 = False
    #print theta
    #print goal
    if flag1 == False:
        print "False:",v_conversion(str(theta),goal.__repr__())

    #print


def FOL_BC_and(KB, goals, theta):
    if theta is None:
        pass
    elif isinstance(goals, list) and len(goals) == 0:
        yield theta
    else:
        if goals.op == '&&':
            first = goals.args[0]
            rest = goals.args[1]
            list_rest = goals.args[1:]
            ref_flag = compare_args(first,list_rest)
            if first.op == '&&':
                while not isPredicate(first):
                    rest = Compound('&&', [first.args[1], rest])
                    first = first.args[0]
        else:
            first = goals
            rest = []
            ref_flag = compare_args(first,rest)
        for theta1 in FOL_BC_or(KB, substitute(theta, first), theta):
            flag = False
            for theta2 in FOL_BC_and(KB, rest, theta1):
                flag = True
                yield theta2
            if not ref_flag and not flag:
                break


'''Execution'''

def main():
    global std_variable_counter
    linesofkb = []
    resultsofqueries = []

    f = open(sys.argv[2],"r")
    #f = open("sample01.txt","r")
    f0 = open("output.txt","w+")

    queries = f.readline().strip()
    queries_list = queries.split(' && ')

    lenofkb = int(f.next().strip())

    while lenofkb > 0:
        expr = f.next().strip()
        linesofkb.append(expr)
        lenofkb -= 1

    parsed_KBlines = map(parse_stmt,linesofkb)
    fin_KB_exprs = map(makeCompound,parsed_KBlines)
    KB = KnowledgeBase(fin_KB_exprs)

    sys.stdout = f0

    query_counter = 0
    while query_counter in range(len(queries_list)):
        curr_Query = makeCompound(parse_stmt(queries_list[query_counter]))
        std_variable_counter = 0
        flag = False
        for curr_result in KB.ask(curr_Query):
            flag = True
            break
        resultsofqueries.append(flag)
        query_counter = query_counter + 1

    #print resultsofqueries
    if False not in resultsofqueries:
        print "True",
    else:
        print "False",

    f0.close()
    f.close()

if __name__ == '__main__':
    main()