#This is a tableau prover made for the Bachelor Project
# made by Oscar de Vries (S2713748)

from tokenize import tokenize, NUMBER, STRING, NAME, OP
from io import StringIO
import sys
import string
import heapq
import os
import subprocess
import timeit

from functools import total_ordering


### Here a list of possible tokens, used for the expression tree ###

# Logical Operators and  their parser input:
# neg = '~'
# and = '&'
# or = '|'
# implication = '>'
# bi implication = '='
# [P] = 'H'
# <P> = 'P'
# [F] = 'G'
# <F> - 'F'
# Absurd = '#'

### Reading the input is done with the following characters:
# infer = '->'
# new premise = ','




#_________________________________________________________________________________________________________________ GLOBALS __________________________________________________________________________________________________________________________________

newWorld = 0
steps = 0
queue = []

operators = ['~','&','|','>','=','H','P','G','F']
modalOperators = ['H','P','G','F']
parentheses = ['(',')']
binaryOperators = ['&','|','>','=']
unaryOperators = ['~','H','P','G','F']
propositions = list(string.ascii_lowercase)
propositions.append('#')

#_________________________________________________________________________________________________________CLASSES AND ABSTRACT DATA TYPES _______________________________________________________________________________________________________________

class Expression:
    def __init__(self, world, tree):
        self.world = world
        self.tree = tree
        self.closed = False
        self.taskAdded = False



    def close_expression(self):
        self.closed = True



class Relation:
    def __init__(self, w1, w2):
        self.w1 = w1
        self.w2 = w2
        self.equal = False
        self.densityAdded = False
        self.addedBy = ''

        def __eq__(self, other):
            if isinstance(other, self.__class__):
                return self.priority == other.priority
            return NotImplemented

        def __lt__(self, other):
            if isinstance(other, self.__class__):
                return self.priority < other.priority
            return NotImplemented


class TableauNode:
    def __init__(self):
        self.expressionList = []
        self.relationList = []
        self.closed = False
        self.parent = None
        self.leftChild = None
        self.rightChild = None
        self.middleChild = None

    def add_expression_to_node(self, expression, world):
        exp = Expression(world,constructTree(expression))
        self.expressionList.append(exp)

    def add_relation_to_node(self, relation):
        self.relationList.append(relation)

    def close_node(self):
        self.closed = True

    def add_leftChild(self):
        self.leftChild = TableauNode()
        self.leftChild.parent = self

    def add_middleChild(self):
        self.middleChild = TableauNode()
        self.middleChild.parent = self


    def add_rightChild(self):
        self.rightChild = TableauNode()
        self.rightChild.parent = self

    def set_parent(self, node):
        self.parent = node

@total_ordering
class QueueItem:
    def __init__(self, priority, expressionLocation,node):
        self.priority = priority
        self.node = node
        self.expLocation = expressionLocation


    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.priority == other.priority
        return NotImplemented

    def __lt__(self, other):
        if isinstance(other, self.__class__):
            return self.priority < other.priority
        return NotImplemented


class ExpTree:
    def __init__(self, value, parent):
        self.value = value
        self.left = None
        self.right = None
        self.child = None
        self.parent = parent
        self.unary = False

class RelationPair:
    def __init__(self, relation1, relation2, type):
        self.r1 = relation1
        self.r2 = relation2
        self.type = type
        self.linearityAdded = False



#_______________________________________________________________________________________________________SMALL FUNCTIONS/HELPER FUNCTIONS _______________________________________________________________________________________________________________


def isUnaryOperator(c):
    if c in unaryOperators:
        return True
    else:
        return False

def isBinaryOperator(c):
    if c in binaryOperators:
        return True
    else:
        return False

def isOperator(c):
    if c in operators:
        return True
    else:
        return False

def remove_double_negation(string):
    newString = string.replace('~~', '')  # removes double negation from string
    return newString

def negate_tree(tree):
    if tree.value == '~':  # double negation, can return child of the first node
        return tree.child
    else:  # top node is not negation, so a new node can be made that has a negation sign, we put the tree under it
        firstNode = ExpTree('~', None)
        firstNode.child = tree
        firstNode.unary = True
        tree.parent = firstNode
        return firstNode

def main_operator_from_tree(tree):
    if tree.value == '~':
        return ('~' + str(tree.child.value))
    else:
        return (tree.value)

def isUniversal(exp):
    if main_operator_from_tree(exp.tree) in ['H', 'G', '~P', '~F']:
        return True
    else:
        return False

def identicalTrees(a, b):
    if a is None and b is None:  # both trees are empty
        return True

    if a is not None and b is not None:  # 2. Both nodes have a value Compare them
        if a.unary and b.unary:  # either the nodes are unary or binary
            # print(a.value + ' ' +b.value)
            return ((a.value == b.value) and
                    identicalTrees(a.child, b.child))
        else:
            # print(a.value + ' ' + b.value)
            return ((a.value == b.value) and
                    identicalTrees(a.left, b.left) and
                    identicalTrees(a.right, b.right))

    return False

def isLiteralTree(r):
    if r.tree.value in propositions or (r.tree.value == '~' and r.tree.child.value in propositions):
        return True
    else:
        return False

def isLiteral(exp):
    if exp in propositions or (exp[0] == '~' and exp[1] in propositions):
        return True
    else:
        return False

#________________________________________________________________________________________________________________ PARSING INPUT _____________________________________________________________________________________________________________________

def parse_input(sentence): #returns premises and negated conclusion in the root of the Tableau
    sentence = ''.join(sentence.split()) #remove all whitespace
    root = TableauNode()

    if '->' in sentence: #there is an inference
        premises = sentence.split('->')[0]
        conclusion = sentence.split('->')[1]
        premiseList = premises.split(',')


        for p in premiseList:
            exp = Expression(0, constructTree(p))
            root.expressionList.append(exp)

        conc = Expression(0, negate_tree(constructTree(conclusion)))
        root.expressionList.append(conc)
    else: #there is only an expression
        print('no infer')
        conc = Expression(0, negate_tree(constructTree(sentence)))
        root.expressionList.append(conc)
    return root

#__________________________________________________________________________________________________________ EXPRESSION TO TREE AND TREE TO EXPRESSION___________________________________________________________________________________________________________

def constructTree(infix):
    tokens = list(infix) #assumption that every binary structure has parentheses around it
    currentNode = ExpTree(None, None) #initialize the root of the tree

    if len(tokens) == 1:
        currentNode.value = tokens[0]
        return currentNode

    for t in tokens:

        if t == '(': #opening parenthesis indicated a binary structure, therefore create two childNodes
            newNode1 = ExpTree(None, currentNode)
            newNode2 = ExpTree(None, currentNode)


            currentNode.left = newNode1
            currentNode.right = newNode2
            currentNode = currentNode.left

        elif isOperator(t):
            if isBinaryOperator(t):
                currentNode.value = t
                currentNode = currentNode.right  #since infix, we know that next token will be whats right of the operator

            if isUnaryOperator(t): #only unary operators will use the 'child' value
                currentNode.unary = True #set node to unary
                currentNode.value = t

                newNode = ExpTree(None, currentNode)
                currentNode.child = newNode

                currentNode = currentNode.child


        elif t in propositions:
            currentNode.value = t
            currentNode = currentNode.parent
            while currentNode != None and currentNode.unary == True: #go to parent as long as node is unary
                if currentNode.parent == None: #In the case that the top node is unary
                    break
                currentNode = currentNode.parent


        elif t == ')':
            if currentNode.parent != None:#final ')' will go to the parent of the root, therefore we do not have to go to the parent of this node
                if currentNode.left == None: #for literals, do go up, for binary operators, do not go up
                    currentNode = currentNode.parent

                while currentNode.parent:
                    if currentNode.unary or currentNode.right.value != None:
                        currentNode = currentNode.parent
                    else:
                        break



    while currentNode.parent: #go all the way up back to the root node before returning
        currentNode = currentNode.parent
    return currentNode



def treeToExpression(tree):
  expression = ""
  if tree != None:
      if tree.unary == False:
          if tree.left != None: #this function makes sure not every atom gets parentheses around it
             expression = '(' + treeToExpression(tree.left)
          else:
             expression = treeToExpression(tree.left)

          expression = expression + str(tree.value)
          if tree.right != None:
             expression = expression + treeToExpression(tree.right)+')'
          else:
             expression = expression + treeToExpression(tree.right)
      if tree.unary == True:
          expression = expression + str(tree.value)
          expression = expression + str(treeToExpression(tree.child))
  return expression



#__________________________________________________________________________________________________________________ADDING TASKS TO QUEUE __________________________________________________________________________________________________________________________________


def add_task_from_node(node):
    if not node.closed:
        for r in node.expressionList:
            if isLiteralTree(r): #node is a literal, don't need to add task
                r.taskAdded = True
            if isUniversal(r): #universal has no rule, can only be applied to existing relations
                r.taskAdded = True
            if r.taskAdded == False:
                # print ('task added for: '+ r.expression)
                operator = main_operator_from_tree(r.tree)
                priority = find_priority(operator)
                q = QueueItem(priority, r, node)
                heapq.heappush(queue, q)
                r.taskAdded = True

def find_priority(operator): #decides which of the 4 degrees of priority the operator belongs to

    prior1 = ['&','~|','~>']
    prior2 = ['F', 'P', '~G', '~H']
    prior3 = ['|','~&','>']
    prior4 = ['=','~=']

    if operator in prior1:
        return 1
    elif operator in prior2:
        return 2
    elif operator in prior3:
        return 3
    elif operator in prior4:
        return 4


#______________________________________________________________________________________________________________ UNUSED FUNCTIONS, MAYBE USEFUL _______________________________________________________________________________________________________________

def find_main_operator(expression): #main operator will be outside the one most outside of the parentheses, thus the lowest parNumber
    parNumber = 0
    opNumber = 99999
    modalOpNumber = 99999
    negNumber = 99999
    modalOperator = None
    operator = None
    neg = False
    i = 0
    tokens = list(expression)
    # print(tokens)

    if len(tokens) <= 1: #eg. an atom
        return 'noOperator'

    for t in tokens:
        if  i<len(tokens) and tokens[i] == '~' and tokens[i + 1] == '~':  # in this case there is a double negation somewhere in the expression, this is surely the first possible operation, thus we can return '~~'
            # print (i)
            # print ('token :'+t)
            # print ('next token :'+ tokens[i+1])
            return '~~'

        if t == '(':
            parNumber +=1
        elif t == ')':
            parNumber -=1

        elif t in operators:
            if t == '~' and parNumber < negNumber: #negation
                neg = True
                negNumber = parNumber


            elif t in modalOperators: #for cases where the modalOperator is the main operator

                if parNumber<modalOpNumber:
                    modalOpNumber = parNumber
                    if i>0 and tokens[i-1] == '~': #modal operator is negated
                        modalOperator = ''.join(['~', t])
                    else:
                        modalOperator = t


            elif parNumber < opNumber and t != '~': #changes the main operator to this token only if the operator is outside of more parentheses than the previous
                opNumber = parNumber
                operator = t

        i += 1


    if operator == None and modalOperator == None: #no value was assigned
        return 'noOperator'

    elif modalOperator and modalOpNumber < opNumber: #when a non-modal operator is on the same parentheses level as  a modal operator, the non-modal is the main operator, therefore this check

        return modalOperator

    elif neg and opNumber == negNumber+1: #returns a negated operator if negation is before the brackets of the main operator, i.e. ~(p & q) returns ~&, but (~p & q) doesn't
        return ''.join(['~', operator])

    return operator

def add_tasks_from_whole_tableau(root):

    if not root.closed:
        for r in root.expressionList:
            if isLiteralTree(r): #node is a literal, don't need to add task
                r.taskAdded = True
            if r.taskAdded == False:
                operator = main_operator_from_tree(r.tree)
                priority = find_priority(operator)
                q = QueueItem(priority, r, root)
                heapq.heappush(queue, q)
                r.taskAdded = True
        if root.leftChild and root.rightChild:
            add_tasks_from_whole_tableau(root.leftChild)
            add_tasks_from_whole_tableau(root.rightChild)

def inOrder(t):
    if t is not None:
        inOrder(t.left)
        print(t.value)
        inOrder(t.right)

class UnaryOperator:
    def __init__(self, operator, parent):
        self.value = operator
        self.parent = parent
        self.child = None
# _____________________________________________________________________________________________________________  TASKS ON EXPRESSIONS ____________________________________________________________________________________________________________________

# ---------------------------Modal tasks: ------------------------------

def world_introducing_operator(TableauNode, expLocation):
    global newWorld
    op = main_operator_from_tree(expLocation.tree)
    expLocation.close_expression()
    newWorld = newWorld + 1

    if op == 'P':
        relation = Relation(newWorld,expLocation.world)
        TableauNode.relationList.append(relation) #new world relates to existing world
        if not_on_branch(Expression(newWorld, expLocation.tree.child), TableauNode):
            TableauNode.expressionList.append(Expression( newWorld, expLocation.tree.child))


    if op == 'F':
        relation = Relation(expLocation.world, newWorld)
        TableauNode.relationList.append(relation) #existing world relates to new world
        if not_on_branch(Expression(newWorld, expLocation.tree.child), TableauNode):
            TableauNode.expressionList.append(Expression( newWorld, expLocation.tree.child))


    if op == '~H':
        relation = Relation(newWorld,expLocation.world)
        TableauNode.relationList.append(relation) #new world relates to existing world
        if not_on_branch(Expression(newWorld, negate_tree(expLocation.tree.child.child)), TableauNode):
            TableauNode.expressionList.append(Expression(newWorld, negate_tree(expLocation.tree.child.child)))


    if op == '~G':
        relation = Relation(expLocation.world, newWorld)
        TableauNode.relationList.append(relation) #existing world relates to new world
        if not_on_branch(Expression(newWorld, negate_tree(expLocation.tree.child.child)), TableauNode):
            TableauNode.expressionList.append(Expression(newWorld, negate_tree(expLocation.tree.child.child)))


    check_contradictions(TableauNode)
    apply_universals_to_new_relation(TableauNode, relation)
    add_linearity_task(TableauNode, relation)
    check_contradictions(TableauNode)
    apply_transitivity(TableauNode, relation)
    check_contradictions(TableauNode)
    add_task_from_node(TableauNode)

    add_density_task(TableauNode)


def apply_universals_to_new_relation(node, relation): #traverses branch and adds universal expressions to current node
    global steps

    node2 = node

    while node2: #traverse full branch, any universal can be applied to new relation
        if not node.closed:
            for exp in node2.expressionList:
                if exp.world == relation.w1: #relations towards the future

                    if main_operator_from_tree(exp.tree) == 'G':
                        steps += 1
                        if not_on_branch((Expression(relation.w2, exp.tree.child)), node):
                            node.expressionList.append(Expression(relation.w2, exp.tree.child))

                    elif main_operator_from_tree(exp.tree) == '~F':
                        steps += 1
                        if not_on_branch(Expression(relation.w2, negate_tree(exp.tree.child.child)), node):
                            node.expressionList.append(Expression(relation.w2, negate_tree(exp.tree.child.child)))
                    check_contradictions(node)


                elif exp.world == relation.w2:  #relations towards the past
                    if main_operator_from_tree(exp.tree) == 'H':
                        steps += 1
                        if not_on_branch((Expression(relation.w1, exp.tree.child)), node):
                            node.expressionList.append(Expression(relation.w1, exp.tree.child))
                    elif main_operator_from_tree(exp.tree) == '~P':
                        steps += 1
                        if not_on_branch(Expression(relation.w1, negate_tree(exp.tree.child.child)), node):
                            node.expressionList.append(Expression(relation.w1, negate_tree(exp.tree.child.child)))
                    check_contradictions(node)

        node2 = node2.parent





# ------------------CONSTRAINTS/RESTRICTIONS: ---------------------

def apply_transitivity(node, relation): # ∀w∀u∀v(wRu∧uRv→wRv)
    node2 = node
    while node2:  # traverse full branch
        for r in node2.relationList:
            if not r.equal:
                if relation.w1 == r.w2:   #if some world already relates to where the new world relates from, also create a relation from where the other world relates from, to where the new world relates to
                    newRelation = Relation(r.w1, relation.w2)
                    newRelation.addedBy = '\\tau'
                    node.relationList.append(newRelation)
                    apply_universals_to_new_relation(node, newRelation)
                    check_contradictions(node)
                elif relation.w2 == r.w1: #for relations to the past
                    newRelation = Relation(relation.w1, r.w2)
                    newRelation.addedBy = '\\tau'
                    node.relationList.append(newRelation)
                    apply_universals_to_new_relation(node, newRelation)
                    check_contradictions(node)

        node2 = node2.parent
    add_density_task(node)

def apply_density(node, relLocation):  #∀w∀u(wRu→∃v(wRv∧vRu))
    global newWorld
    newWorld = newWorld + 1

    newRelation1 = Relation(relLocation.w1,newWorld)
    newRelation2 = Relation(newWorld, relLocation.w2)
    newRelation1.addedBy = '\\delta'
    newRelation2.addedBy = '\\delta'
    node.relationList.append(newRelation1)
    node.relationList.append(newRelation2)
    apply_universals_to_new_relation(node, Relation(relLocation.w1,newWorld))
    apply_universals_to_new_relation(node, Relation(newWorld,relLocation.w2))
    apply_universals_to_new_relation(node, Relation(relLocation.w1,newWorld))
    check_contradictions(node)

    add_linearity_task(node, newRelation1)
    add_linearity_task(node, newRelation2)
    add_density_task(node)

def apply_forward_convergent(node,rel1,rel2):#∀w∀u∀v((wRu∧wRv→(uRv ∨ v=u ∨ vRu))
    if node.leftChild == None and node.rightChild == None: #node is a leaf, add left , middle and right child, and append the relations there
        if not node.closed:
            node.add_rightChild()
            node.add_leftChild()
            node.add_middleChild()

            newRelation1 = Relation(rel1.w2, rel2.w2)
            newRelation2 = Relation(rel2.w2, rel1.w2)
            newRelation3 = Relation(rel1.w2, rel2.w2)
            newRelation3.equal = True

            newRelation1.addedBy = '\\varphi'
            newRelation2.addedBy = '\\varphi'
            newRelation3.addedBy = '\\varphi'

            node.leftChild.relationList.append(newRelation3) #w1=w2
            node.middleChild.relationList.append(newRelation1) #w1rw2
            node.rightChild.relationList.append(newRelation2) #w2rw1
            add_equal_expressions(node.leftChild, newRelation3)
            apply_universals_to_new_relation(node.middleChild, Relation(rel1.w2, rel2.w2))
            apply_universals_to_new_relation(node.rightChild, Relation(rel2.w2, rel1.w2))

    else:               #traverses the childs of the node and repeats the process untill leaves are found
        apply_forward_convergent(node.leftChild, rel1, rel2)
        if node.middleChild:
            apply_forward_convergent(node.middleChild, rel1, rel2)
        apply_forward_convergent(node.rightChild, rel1, rel2)


def apply_backward_convergent(node, rel1, rel2):  #∀w∀u∀v((wRu∧vRu→(wRv ∨ w=v ∨ vRw))


    if node.leftChild == None and node.rightChild == None:  # node is a leaf, add left , middle and right child, and append the relations there
        if not node.closed:
            node.add_rightChild()
            node.add_leftChild()
            node.add_middleChild()

            newRelation1 = Relation(rel1.w1, rel2.w1)
            newRelation2 = Relation(rel2.w1, rel1.w1)
            newRelation3 = Relation(rel1.w1, rel2.w1)
            newRelation3.equal = True

            newRelation1.addedBy = '\\beta'
            newRelation2.addedBy = '\\beta'
            newRelation3.addedBy = '\\beta'

            node.leftChild.relationList.append(newRelation3) #w1=w2
            node.middleChild.relationList.append(newRelation1)#w1rw2
            node.rightChild.relationList.append(newRelation2) #w2rw1
            add_equal_expressions(node.leftChild, newRelation3)
            apply_universals_to_new_relation(node.middleChild, Relation(rel1.w1, rel2.w1))
            apply_universals_to_new_relation(node.rightChild, Relation(rel2.w1, rel1.w1))

    else:  # traverses the childs of the node and repeats the process untill leaves are found
        apply_backward_convergent(node.leftChild, rel1, rel2)
        if node.middleChild:
            apply_backward_convergent(node.middleChild, rel1, rel2)
        apply_backward_convergent(node.rightChild, rel1, rel2)


def add_density_task(node):
    if not node.closed:
        for r in node.relationList:
            if not r.equal:
                if r.densityAdded == False:
                    q = QueueItem(6, r, node)
                    heapq.heappush(queue, q)
                    r.densityAdded = True

def add_linearity_task(node, relation):

    node2 = node
    while node2:

        if not node2.closed:
            for r in node2.relationList:
                # print(str(r.w1) + 'R' + str(r.w2))
                if not r.equal:
                    if r.w1 == relation.w1 and r.w2 != relation.w2: #forward convergent
                        # print('forward converging task!')
                        relPair = RelationPair(r, relation, 'f')
                        q = QueueItem(5, relPair, node)
                        heapq.heappush(queue, q)
                    elif r.w2 == relation.w2 and r.w1 != relation.w1: #backward convergent
                        # print('backward converging task!')
                        relPair = RelationPair(r, relation, 'b')
                        q = QueueItem(5, relPair, node)
                        heapq.heappush(queue, q)
        node2 = node2.parent

def add_equal_expressions(node, relation): #for equal worlds add every expression that has one of the worlds with the other world

    node2 = node
    while node2:
        if not node.closed:
            for exp in node2.expressionList:
                if exp.world == relation.w1:
                    if not_on_branch((Expression(relation.w2, exp.tree)), node):
                        node.expressionList.append(Expression(relation.w2, exp.tree))
                elif exp.world == relation.w2:
                    if not_on_branch((Expression(relation.w1, exp.tree)), node):
                        node.expressionList.append(Expression(relation.w1, exp.tree))
                check_contradictions(node)
        node2 = node2.parent




#----------------------Non Modal Tasks: ---------------------------------------------

def disjunction(TableauNode, expLocation): #concept of dividing a distribution, close expression and add outcome of task to new branches, or to same branch
    tree = expLocation.tree #construct tree from expression
    expLocation.close_expression()


    exp1 = tree.left
    exp2 = tree.right


    if main_operator_from_tree(tree) == '|':
        add_disjunction_to_leaves(TableauNode, exp1, exp2, expLocation.world)

    elif main_operator_from_tree(tree) == '~&': #negates both expressions
        exp3 = negate_tree(tree.child.left)
        exp4 = negate_tree(tree.child.right)
        add_disjunction_to_leaves(TableauNode, exp3, exp4, expLocation.world)


    elif main_operator_from_tree(tree) == '>': #negates antecedent expression
        exp3 = negate_tree(tree.left)
        add_disjunction_to_leaves(TableauNode, exp3, exp2, expLocation.world)

def biconditional(TableauNode, expLocation): #concept of dividing a distribution, close expression and add outcome of task to new branches, or to same branch
    tree = expLocation.tree #construct tree from expression
    expLocation.close_expression()


    if main_operator_from_tree(tree) == '=':
        exp1 = tree.left
        exp2 = tree.right
        exp3 = negate_tree(tree.left)
        exp4 = negate_tree(tree.right)

        add_bi_implication_to_leaves(TableauNode, exp1, exp2, exp3, exp4, expLocation.world) # (a=b) returns a,b in left child and ~a,~b in right child

    elif main_operator_from_tree(tree)== '~=':
        exp1 = tree.child.left
        exp2 = tree.child.right
        exp3 = negate_tree(tree.child.left)
        exp4 = negate_tree(tree.child.right)
        add_bi_implication_to_leaves(TableauNode, exp1, exp4, exp2, exp3, expLocation.world)# ~(a=b) returns a,~b in left child and ~a,b in right child


def add_disjunction_to_leaves(node, disjunct1, disjunct2, world):

    if node.leftChild == None and node.rightChild == None: #node is a leaf, add left and right child, and append the disjuncts there
        if not node.closed:
            node.add_leftChild()
            node.leftChild.parent = node
            node.add_rightChild()
            node.rightChild.parent = node
            if not_on_branch((Expression(world, disjunct2)), node):
                node.rightChild.expressionList.append(Expression(world, disjunct2))
            if not_on_branch((Expression(world, disjunct1)), node):
                node.leftChild.expressionList.append(Expression(world, disjunct1))


            check_contradictions(node.leftChild)  #check if new added expression causes a contradiction, if so, close branches
            check_contradictions(node.rightChild)

            add_task_from_node(node.leftChild) #adds tasks
            add_task_from_node(node.rightChild)

    else:               #traverses the childs of the node and repeats the process untill leaves are found
        add_disjunction_to_leaves(node.leftChild, disjunct1, disjunct2, world)
        if node.middleChild:
            add_disjunction_to_leaves(node.middleChild, disjunct1, disjunct2, world)
        add_disjunction_to_leaves(node.rightChild, disjunct1, disjunct2, world)


def add_bi_implication_to_leaves(node, exp1, exp2, exp3, exp4, world):

    if node.leftChild == None and node.rightChild == None: #node is a leaf, add left and right child, and append the expressions here
        if not node.closed:
            node.add_leftChild()
            node.leftChild.parent = node
            if not_on_branch((Expression(world,exp1)), node):
                node.leftChild.expressionList.append(Expression(world,exp1))
            if not_on_branch((Expression(world, exp2)), node):
                node.leftChild.expressionList.append(Expression(world,exp2))
            node.add_rightChild()
            node.rightChild.parent = node
            if not_on_branch((Expression(world, exp3)), node):

                node.rightChild.expressionList.append(Expression(world,exp3))
            if not_on_branch((Expression(world, exp4)), node):
                node.rightChild.expressionList.append(Expression(world,exp4))

            check_contradictions(node.leftChild)  #check if new added expressions cause a contradiction, if so, close branches
            check_contradictions(node.rightChild)

            add_task_from_node(node.leftChild) #adds tasks
            add_task_from_node(node.rightChild)

    else:               #traverses the childs of the node and repeats the process untill leaves are found
        add_bi_implication_to_leaves(node.leftChild, exp1, exp2, exp3, exp4, world)
        if node.middleChild:
            add_bi_implication_to_leaves(node.middleChild, exp1, exp2, exp3, exp4, world)
        add_bi_implication_to_leaves(node.rightChild, exp1, exp2, exp3, exp4, world)


def conjunction(TableauNode, expLocation): #for conjunction tasks, including negated disjunction and negated implication

    tree = expLocation.tree #construct tree from expression
    expLocation.close_expression()

    if main_operator_from_tree(tree) == '&':
        exp1 = tree.left
        exp2 = tree.right

    elif main_operator_from_tree(tree) == '~|':
        exp1 = negate_tree(tree.child.left)
        exp2 = negate_tree(tree.child.right)

    elif main_operator_from_tree(tree) == '~>':
        exp1 = tree.child.left
        exp2 = negate_tree(tree.child.right)

    if not_on_branch(Expression(expLocation.world,exp1), TableauNode):
        TableauNode.expressionList.append(Expression(expLocation.world,exp1))  #we can add the expressions to the same node
    if not_on_branch(Expression(expLocation.world,exp2), TableauNode):
        TableauNode.expressionList.append(Expression(expLocation.world,exp2))

    check_contradictions(TableauNode)  #check if new expressions form a contradiction
    add_task_from_node(TableauNode)  # adds tasks





#________________________________________________________________________________________________________________ CONTRADICTION CHECK _____________________________________________________________________________________________________________________

def check_contradictions(node): #for all expressions on a node, check whether the expression makes a contradiction with another expression on it's own node, or further above on the tableau.

    for expression1 in node.expressionList:
        if traverse_branch(node,expression1):
            close_leaves(node)
            break

def close_leaves(root):
    if root.leftChild == None and root.rightChild == None:  #if a contradiction is found further up the branch, all leaves must be closed
        root.close_node()

    else:
        if root.middleChild != None:
            close_leaves(root.leftChild)
            close_leaves(root.middleChild)
            close_leaves(root.rightChild)
        else:
            close_leaves(root.leftChild)
            close_leaves(root.rightChild)


def traverse_branch(node, exp1): #First checks the expressions on the node itself, if that doesn't cause a contradiction, check for expressions on parent node

    while node is not None:

        for exp2 in node.expressionList:
            if exp2.tree.value == '#': #absurd
                return True

            if exp1.world == exp2.world:
                if exp2.tree.value == '~' and exp1.tree.value != '~':
                    if identicalTrees(exp1.tree, exp2.tree.child):
                        return True
                elif exp2.tree.value != '~' and exp1.tree.value == '~':

                    if identicalTrees(exp1.tree.child,exp2.tree):
                        return True


        node = node.parent

    return False #no contradictions found on branch

def check_tableau_closed(root): #checks whether all leave nodes are closed

        if root.leftChild == None and root.rightChild == None:  # node is a leaf, check if it is closed
            if root.closed:
                return True

        else:
            if root.middleChild != None:
                if check_tableau_closed(root.leftChild) and check_tableau_closed(root.middleChild) and check_tableau_closed(root.rightChild):
                    return True
            elif check_tableau_closed(root.leftChild) and check_tableau_closed(root.rightChild):
                return True


        return False


# ___________________________________________________________________________________________________________ COUNTER MODEL ________________________________________________________________________________________________________

def show_counter_model(root): # find first open branch and show counter model
    if root.leftChild == None and root.rightChild == None :  # node is a leaf and it is not closed
        if not root.closed:
            print_literals(root)
            return True

    else:
        if root.middleChild != None:
            if show_counter_model(root.leftChild) or show_counter_model(root.middleChild) or show_counter_model(root.rightChild):
                return True
        elif show_counter_model(root.leftChild) or show_counter_model(root.rightChild):
            return True

    return False

def print_literals(root):
    p = []


    while root is not None:
        index = 0
        for exp in root.expressionList:
            if exp.closed:
                x = 'X'
            else:
                x = ''
            if isLiteralTree(exp):  # only append literals
                p.append(treeToExpression(exp.tree)+','+str(exp.world))



        root = root.parent



    p = list(set(p))  # remove duplicates

    print('\nCountermodel:')
    for item in p:
        print(item+'\t',end='', flush=True)



#__________________________________________________________________________________________________________________ SHOW TABLEAU______________________________________________________________________________________________

def find_open_branch(root, infBreak):
    if root.leftChild == None and root.rightChild == None :  # node is a leaf and it is not closed
        if not root.closed:
            show_counter_model2(root, infBreak)
            return True

    else:
        if root.middleChild != None:
            if find_open_branch(root.leftChild, infBreak) or find_open_branch(root.middleChild, infBreak) or find_open_branch(root.rightChild, infBreak):
                return True
        elif find_open_branch(root.leftChild, infBreak) or find_open_branch(root.rightChild, infBreak):
            return True
    return False



def print_literals_latex(root):
    p = []
    worlds = []
    root2 = root
    root3 = root
    while root2 is not None:

        for exp in root2.expressionList:
            if isLiteralTree(exp):  # only append literals
                p.append(treeToExpression(exp.tree) + ',' + str(exp.world))
                worlds.append(exp.world)

        root2 = root2.parent

    p = list(set(p))  # remove duplicates

    f.write('Literals \\\\\n')
    f.write('$\n')

    for item in p:
        negLiteral = item.replace('~','\\neg ')
        f.write(negLiteral+'\\quad ')

    f.write('$\n')

    f.write('\\\\\nRelations: \\\\\n')

    check = False
    while root3 is not None:
        for rel in root3.relationList:
            if  rel.w1 in worlds or rel.w2 in worlds:
                if check == False:
                    f.write('$\n')
                    check = True
                if rel.equal:
                    f.write('w_{'+str(rel.w1) + '}=w_{' + str(rel.w2) + '} \\, ('+rel.addedBy+')\\quad')
                else:
                    f.write('w_{' + str(rel.w1) + '}Rw_{' + str(rel.w2) + '} \\, (' + rel.addedBy + ')\\quad')
        root3 = root3.parent

    if check:
        f.write('$\n')

def show_counter_model2(root, infBreak):
    worlds = []
    literals = []
    root2 = root
    root3 = root

    while root2 is not None:
        for exp in root2.expressionList:
            if isLiteralTree(exp):  # only append literals
                literals.append(exp)
                worlds.append(exp.world)

        root2 = root2.parent


    check = False

    literals = list(set(literals))
    worlds = list(set(worlds))

    f.write('\\\\\n \\textbf{W:} \\\\\n ')
    f.write('$\n')

    commaCheck = False
    for item in worlds:
        if commaCheck == True:
            f.write(',\\quad ')
        commaCheck = True
        f.write('w_{'+str(item)+'}')

    commaCheck = False

    if infBreak:
        f.write(', \\quad ... \\quad , \\quad \\infty')

    f.write('$\n')
    f.write('\\\\\n \\textbf{R:} \\\\\n ')

    while root3 is not None:
        for rel in root3.relationList:
            if  rel.w1 in worlds or rel.w2 in worlds:
                if check == False:
                    f.write('$\n')
                    check = True
                if commaCheck == True:
                    f.write(',\\quad ')
                commaCheck = True
                if rel.equal:
                    f.write('w_{'+str(rel.w1) + '}=w_{' + str(rel.w2) + '} \\, ('+rel.addedBy+')\\quad')
                else:
                    f.write('w_{' + str(rel.w1) + '}Rw_{' + str(rel.w2) + '} \\, (' + rel.addedBy + ')\\quad')
        root3 = root3.parent


    if check:
        f.write('$\n')

    commaCheck = False

    f.write('\\\\\n \\textbf{v:} \\\\\n ')
    f.write('$\n')
    valuations = []
    for l in literals:

        if l.tree.value == '~':
            valuations.append('v_{w_{'+str(l.world)+'}}('+l.tree.child.value+') = 0')
        else:
            valuations.append('v_{w_{' + str(l.world) + '}}(' + l.tree.value + ') = 1')


    valuations = list(set(valuations))
    for v in valuations:
        if commaCheck == True:
            f.write(',\\quad ')
        commaCheck = True
        f.write(v)

    f.write('$\n')


def show_tableau(root):
    index = 0
    deltaCount = 0

    if(root == None):
        return
    f.write("[.{\n")

    for exp in root.expressionList:
        f.write('$')
        printExpTreeLatex(exp.tree)
        f.write("," +str(exp.world)+"$\\\\\n")


    for rel in root.relationList:
        f.write('$')
        if rel.addedBy == '\\delta':
            deltaCount += 1
        else:
            deltaCount = 0

        if deltaCount == 5:
            f.write('\\vdots$\\\\\n $\\infty$\\\\\n')
            break

        if rel.equal:
            f.write(str(rel.w1) + '=' + str(rel.w2)+' \\,'+rel.addedBy+'$\\\\\n')
        else:
            f.write(str(rel.w1) + 'r' + str(rel.w2) +' \\,' + rel.addedBy + '$\\\\\n')


    f.write("} \n")

    if root.leftChild == None and root.rightChild == None:
        if root.closed:
            f.write('$\\times$')
    else:
        show_tableau(root.leftChild)
        if root.middleChild:
            show_tableau(root.middleChild)
        show_tableau(root.rightChild)

    f.write(" ]\n")

def printExpTreeLatex(tree):
    if tree == None:
        return

    if tree.value == '#':
        f.write('\\bot ')
    elif tree.value in propositions:
        f.write (tree.value)
    elif tree.value == '|':
        f.write('(')
        printExpTreeLatex(tree.left)
        f.write('\\lor ')
        printExpTreeLatex(tree.right)
        f.write(')')
    elif tree.value == '&':
        f.write('(')
        printExpTreeLatex(tree.left)
        f.write('\\land ')
        printExpTreeLatex(tree.right)
        f.write(')')
    elif tree.value == '~':
        f.write('\\neg ')
        printExpTreeLatex(tree.child)
    elif tree.value == '>':
        f.write('(')
        printExpTreeLatex(tree.left)
        f.write('\\to ')
        printExpTreeLatex(tree.right)
        f.write(')')
    elif tree.value == '=':
        f.write('(')
        printExpTreeLatex(tree.left)
        f.write('\\leftrightarrow ')
        printExpTreeLatex(tree.right)
        f.write(')')
    elif tree.value in modalOperators:
        f.write(tree.value)
        printExpTreeLatex(tree.child)


def printLatexPageStart():
    f.write("\\documentclass{article}\n")
    f.write("\\usepackage[utf8]{inputenc}\n")
    f.write("\\usepackage{amsmath}\n")
    f.write("\\usepackage{amsfonts}\n")
    f.write("\\usepackage{qtree}\n")
    f.write("\\usepackage{graphicx}\n")
    f.write("\\usepackage{soul}\n")
    f.write("\\usepackage{fullpage}\n\n")
    f.write("\\begin{document}\n\n")

def printLatexPageEnd():
    f.write("\n\n\\end{document}\n")

def printLatexPageContent(root, input, closed, tableauNumber, infBreak, denseworld1, denseworld2):
    global f
    with open('workfile.tex', 'w') as f:
        printLatexPageStart()
        f.write("\\textbf{Input:}\\\\\n $")
        inputToLatex(input)
        f.write("$.\\\\\n")
        f.write("\n\\textbf{Semantic tableau:}\\\ \n")
        f.write("\\resizebox*{\\linewidth}{0.8\\textheight}{\n")
        f.write("\\Tree ")
        show_tableau(root)
        f.write("}\\\\\n")
        if not closed:
            f.write('\nTableau open, inference is not valid\\\\\n')
            f.write("\n\\textbf{Counter-Model, a dense and transitive model $<W,R,v>$ read off from open branch:} \\\\\n")
            find_open_branch(root, infBreak)
            if infBreak:
                f.write('\\\\\nR is the dense and transitive closure of [$w_{'+str(denseworld1)+'},....,w_{'+str(denseworld2)+'}$] as in Q\\\\\n')


        else:
            f.write('\nTableau closed, inference is valid\\\\\n')

        printLatexPageEnd()

    create_pdf('workfile.tex', 'output'+str(tableauNumber))
    os.startfile('output'+str(tableauNumber)+'.pdf')


def inputToLatex(input):
    input = ''.join(input.split())  # remove all whitespace
    comma = False

    if '->' in input:  # there is an inference
        premises = input.split('->')[0]
        conclusion = input.split('->')[1]
        premiseList = premises.split(',')

        for p in premiseList:
            if comma:
                f.write(',')
            printExpTreeLatex(constructTree(p))
            comma = True

        f.write('\\vdash_{K^t_{\\tau\\delta\\varphi\\beta}} ')
        printExpTreeLatex(constructTree(conclusion))

    else:  # there is only an expression
        f.write('\\vdash_{K^t_{\\tau\\delta\\varphi\\beta}} ')
        printExpTreeLatex(constructTree(input))

def create_pdf(input_filename, output_filename):

    process = subprocess.Popen([
        r'C:\Program Files\MiKTeX\miktex\bin\x64\latex.exe',
        '-output-format=pdf',
        '-job-name=' + output_filename,
        input_filename],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
         )
    process.wait()


#________________________________________________________________________________________________________________CHECK DENSITY AMOUNT____________________________________________________________________________________________
def check_density_amount(input, arguments):
    minG = 99999
    minH = 99999
    maxG = 0
    maxH = 0


    for argument in arguments:
        gCount = 0
        hCount = 0
        for t in list(treeToExpression(argument.tree)):  #Stores maximal amount of G or H found in an argument
            if t == 'G':
                gCount += 1
            elif t == 'H':
                hCount += 1

        if gCount: #at least one G has occurred in argument
            if gCount > maxG:
                maxG = gCount
            if gCount < minG:
                minG = gCount

        if hCount: #at least one H has occurred in argument
            if hCount > maxH:
                maxH = hCount
            if hCount < minH:
                minH = hCount

    difH = maxH - minH
    difG = maxG - minG

    highestDif = max(difH, difG)
    if highestDif > 4:
        return highestDif
    else:
        return 4

#________________________________________________________________________________________________________________REMOVE DOUBLE FORMULAS___________________________________________________________________________________________
def not_on_branch(exp1, node):
    global doubleFormulaCheck

    if not doubleFormulaCheck:
        return True

    while node is not None:
        for exp2 in node.expressionList:
            if exp1.world == exp2.world:
                if identicalTrees(exp1.tree, exp2.tree): #identical expression already on branch
                    return False

        node = node.parent

    return True #expression not on branch yet

#________________________________________________________________________________________________________________APPLY TASKS____________________________________________________________________________________________

def applyTask(item):
    global steps
    if item.priority == 1:
        conjunction(item.node, item.expLocation)
        steps += 1
    elif item.priority == 2:
        world_introducing_operator(item.node, item.expLocation)
        steps += 1
    elif item.priority == 3:
        disjunction(item.node, item.expLocation)
        steps += 1
    elif item.priority == 4:
        biconditional(item.node, item.expLocation)
        steps += 1
    elif item.priority == 5:
        if item.expLocation.type == 'f':
            apply_forward_convergent(item.node, item.expLocation.r1, item.expLocation.r2)
        elif item.expLocation.type == 'b':
            apply_backward_convergent(item.node, item.expLocation.r1, item.expLocation.r2)
        steps += 1
    elif item.priority == 6:
        apply_density(item.node, item.expLocation)
        steps += 1
#____________________________________________________________________________________________________________ MAIN FUNCTION ______________________________________________________________________________________________

def main(argv):
    global queue
    global newWorld
    global steps
    global doubleFormulaCheck
    tableauNumber=0

    print ("Type a logical inference (p1,p2,...,pn->C) or '!' to quit:")

    for line in sys.stdin:
        doubleFormulaCheck = True
        start = timeit.default_timer()
        infBreak = False
        maxLinear = False
        firstDensity = True
        denseworld1 = None
        denseworld2 = None
        minRunTime = 90
        tableauNumber += 1
        steps = 0
        densityCheck = 0
        linearityCheck = 0
        newWorld = 0
        queue = []
        closed = False

        if line == "!\n":
            print("Bye!")
            sys.exit()


        ### initial input handling
        input = ''.join(line.split()) #save for final print
        line = remove_double_negation(line) #double negations can be removed from the string
        root = parse_input(line)
        add_task_from_node(root)
        check_contradictions(root)

        deltaIteration = check_density_amount(input, root.expressionList) #determine how many times density can be applied

        ### main loop in program
        while queue:

            if check_tableau_closed(root):
                closed = True
                break

            item = heapq.heappop(queue)

            if item.priority == 6:
                linearityCheck = 0
                densityCheck +=1
                if densityCheck >= deltaIteration:  #Break if density is applied too many times in a row or only linearity is applied in between, indicating infinity
                    infBreak = True
                    print('Quit due to infinite density')
                    break

                if firstDensity:
                    firstDensity = False
                    denseworld1 = item.expLocation.w1
                    denseworld2 = item.expLocation.w2


            if item.priority <5:
                densityCheck = 0
                linearityCheck = 0

            if item.priority == 5:
                linearityCheck+=1
                if linearityCheck == 4:
                    maxLinear = True

                if not maxLinear: #if linearity is not yet applied too many times.
                    applyTask(item)
                elif start < minRunTime: #apply linearity at least until 1.5 minutes run time
                    applyTask(item)

            else:
                applyTask(item)

        check_contradictions(root)  #final check, contradiction might occur after all the tasks are done

        if check_tableau_closed(root):
            closed = True
            print('Tableau closed, inference is valid')

        if not closed:
            print ('Tableau open, inference is not valid')
            show_counter_model(root)

        stop = timeit.default_timer()
        print ('\ntime to compute: '+str(stop-start))
        print('number of expressions expanded: ' + str(steps))


        # printLatexPageContent(root, input, closed,tableauNumber, infBreak, denseworld1, denseworld2)


        print("Type a logical sentence or '!' to quit:")

    print ('Bye!')

if __name__ == "__main__":
    main(sys.argv)


