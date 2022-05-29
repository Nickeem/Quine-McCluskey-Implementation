# QuineMcCluskey Algorithm based on wikipedia implementation
# https://en.wikipedia.org/wiki/Quine%E2%80%93McCluskey_algorithm
class QuineMcCluskey:

    def __init__(self, min_terms=(), no_of_variables=0):
        self.minTerms = ()
        self.minTerms_table = {}
        self.BITS = 0
        self.terms = ()
        self.expression = ""  # min_term function
        self.max_term = 0
        self.num_of_ones_table = 0
        self.implicants = {2: {}}
        self.implicants_sets = {2: []}
        self.implicants_referencer = {}
        self.size_implicants_table = []
        self.prime_implicants = []
        self.essential_implicants = []
        self.final_implicants = []
        self.simple_expression = ""
        self.prime_implicants_table = []

        if min_terms == ():
            return
        self.setup(min_terms, no_of_variables)

    def initialize(self):
        self.minTerms = ()
        self.minTerms_table = {}
        self.BITS = 0
        self.terms = ()
        self.expression = ""  # min_term function
        self.max_term = 0
        self.num_of_ones_table = 0
        self.implicants = {2: {}}
        self.implicants_sets = {2: []}
        self.implicants_referencer = {}
        self.size_implicants_table = []
        self.prime_implicants = []
        self.essential_implicants = []
        self.final_implicants = []
        self.simple_expression = ""
        self.prime_implicants_table = []

    def setup(self, min_terms, no_of_variables=0):
        if type(min_terms) is not tuple:
            return
        self.initialize()
        self.minTerms = min_terms  # min_terms must be a tuple
        if no_of_variables == 0 or max(min_terms) > 2**no_of_variables:
            self.BITS = len(bin(max(self.minTerms))[2:])
        else:
            self.BITS = no_of_variables
        self.binary_dict()
        self.terms = tuple("ABCDEFGHIJKLMNOPQRSTUVWXYZ"[:self.BITS])
        self.create_expression()
        self.max_term = 2 ** self.BITS
        self.visual()
        self.size_2_implicants()
        if self.implicants[2] == {}:
            for m in self.minTerms:
                self.final_implicants.append(m)
            self.simple_expression_creator(self.final_implicants)
            # self.pi_table_creator() not necessary
            return

        self.additional_implicants(2)
        for x in list(self.implicants.values()):
            if ("-"*self.BITS) in x.values():
                self.final_implicants.append(1)
                self.simple_expression = "1"
                return
        for i in list(self.implicants.values()):
            for x in i:
                self.implicants_referencer[x] = i[x]
        self.prime_implicants_finder()
        self.size_implicants_table_creator()
        self.final()
        self.simple_expression_creator(self.final_implicants)
        self.pi_table_creator()

    def pi_table_creator(self):
        headers = ["Impliacnts"]
        for i in self.minTerms:
            headers.append(i)
        headers.append("Expression")
        rows = [headers]
        for implicant in self.prime_implicants:
            data = [str(implicant)]
            if implicant in self.essential_implicants:
                data[0] = data[0] + "*"
            for m in self.minTerms:
                if m in implicant:
                    data.append("x")
                else:
                    data.append("")
            data.append(self.implicants_referencer[str(implicant)])
            rows.append(data)
        self.prime_implicants_table = rows

    def simple_expression_creator(self, data):
        def statement_generator(expr):
            string = ""
            for i in range(len(expr)):
                if expr[i] == '-':
                    continue
                string += self.terms[i]
                if expr[i] == '0':
                    string += "'"
            return string

        expressions = []
        for i in data:
            if type(i) is int:
                b = bin(i)[2:]
                b = ('0' * (self.BITS - len(b))) + b
                expressions.append(statement_generator(b))
            elif type(i) is set:
                expressions.append(statement_generator(self.implicants_referencer[str(i)]))
        self.simple_expression += ' + '.join(expressions)

    def final(self):
        def weights(accounted_for=set({}), implicants_to_choose_from=[]):
            if tuple(accounted_for) == self.minTerms:
                return
            if not implicants_to_choose_from:  # min term not accounted for
                if tuple(accounted_for) != self.minTerms:
                    for minterm in self.minTerms:
                        if minterm not in accounted_for:
                            self.final_implicants.append(minterm)
                return
            weight = {}
            heaviest = 0
            to_add = set({})
            for im in implicants_to_choose_from:
                weight[str(im)] = 0
            for imp in implicants_to_choose_from:
                for t in imp:
                    if t not in accounted_for:
                        weight[str(imp)] += 1
                        if weight[str(imp)] > heaviest:
                            heaviest = weight[str(imp)]
                            to_add = imp
            self.final_implicants.append(to_add)
            implicants_to_choose_from.remove(to_add)
            accounted_for = accounted_for.union(to_add)
            weights(accounted_for, implicants_to_choose_from)

        essential = {}
        for term in self.minTerms:
            essential[term] = 0
        e_implicants = {}
        for implicant in self.prime_implicants:
            for term in implicant:
                if term not in essential:
                    continue
                e_implicants[term] = implicant
                essential[term] += 1
                if essential[term] > 1:
                    essential.pop(term)
                    e_implicants.pop(term)

        self.essential_implicants = list(e_implicants.keys())
        ag = set({})  # terms accounted for
        for implicant in e_implicants.values():
            if implicant in self.final_implicants:
                continue
            self.final_implicants.append(implicant)
            ag = ag.union(implicant)
        # print(self.final_implicants)
        implicants_tcf = self.prime_implicants.copy()
        for elem in self.final_implicants:
            if elem in implicants_tcf:
                implicants_tcf.remove(elem)

        weights(ag, implicants_tcf)

    def size_implicants_table_creator(self):
        table = [["Size", "Implicant", "Expression"]]
        for size in self.implicants:
            for implicant in self.implicants[size]:
                table.append([size, implicant, self.implicants[size][implicant]])
        self.size_implicants_table = table

    def binary_dict(self):
        for i in self.minTerms:
            i_bin = bin(i)[2:]  # i in binary from
            mb = self.BITS - len(i_bin)  # missing bits
            self.minTerms_table[i] = (mb * "0") + i_bin  # add missing bits to string if necessary

    def create_expression(self):
        self.expression = "Expression: "
        self.expression += "F"
        self.expression += str(self.terms).replace("'", "")
        self.expression += " = "
        self.simple_expression = ("Simplified " + self.expression)
        for min_term, bin_num in self.minTerms_table.items():
            for i in range(self.BITS):
                self.expression += self.terms[i]
                if bin_num[i] == '0':  # checks bit
                    self.expression += "'"
            self.expression += " + "

        self.expression = self.expression[:-3]  # last statement in loop is run 1 more than needed

    def visual(self):
        no1 = {}
        for i in self.minTerms_table:
            ones = self.minTerms_table[i].count('1')
            if ones not in no1:
                no1[ones] = []
            no1[ones].append(i)

        data = [["number of 1's", "minterm", "binary"]]
        for i in no1:
            for min_term in no1[i]:
                data.append([i, min_term, self.minTerms_table[min_term]])
        self.num_of_ones_table = data  # tabulate(data, headers='firstrow', tablefmt='pipe')
        # print(data)

    def bit_difference(self, bin1, bin2):
        bit_diff = {"count": 0, "index": []}
        for i in range(self.BITS):
            if bin1[i] != bin2[i]:
                bit_diff["count"] += 1
                bit_diff["index"].append(i)
        return bit_diff

    def size_2_implicants(self):
        size = 2
        for min_term in self.minTerms_table:
            for s_term in self.minTerms_table:
                # s_term - second term to be in set
                s = {min_term, s_term}
                if len(s) < 1 or str(s) in self.implicants[size]:
                    continue

                diff_count = 0
                index = 40
                for i in range(self.BITS):  # look for different terms with a difference of 1 bit
                    if self.minTerms_table[min_term][i] != self.minTerms_table[s_term][i]:
                        diff_count += 1
                        index = i
                    if diff_count > 1:
                        break
                if diff_count == 1:
                    if size not in self.implicants:
                        self.implicants[size] = {}
                    implicant = list(self.minTerms_table[min_term])
                    implicant[index] = "-"
                    self.implicants[size][str(s)] = ''.join(implicant)
                    self.implicants_sets[size].append(s)  # used to find future sized implicants 2^n

    def additional_implicants(self, n):
        size = 2 ** n
        pr_size = 2 ** (n - 1)
        if size not in self.implicants:
            self.implicants[size] = {}
            self.implicants_sets[size] = []

        for implicant in self.implicants_sets[pr_size]:
            for s_implicant in self.implicants_sets[pr_size]:
                n_implicant = implicant | s_implicant  # combine sets
                if len(n_implicant) < size or n_implicant in self.implicants_sets[pr_size]:
                    continue
                bit_diff = self.bit_difference(self.implicants[pr_size][str(implicant)],
                                               self.implicants[pr_size][str(s_implicant)])
                if bit_diff["count"] == 1:
                    new_term = list(self.implicants[pr_size][str(implicant)])
                    new_term[bit_diff["index"][0]] = "-"
                    new_term = ''.join(new_term)
                    self.implicants[size][str(n_implicant)] = new_term
                    self.implicants_sets[size].append(n_implicant)
                    # need to add recursive part
        if self.implicants[size] != {}:
            self.additional_implicants(n + 1)
        else:
            self.implicants.pop(size)
        # else return because no further implicants will be found

    def prime_implicants_finder(self):
        sizes = list(self.implicants.keys())[::-1]
        min_terms = list(self.minTerms)
        for size in sizes:
            for implicant in self.implicants_sets[size]:
                popped = False
                for min_term in implicant:
                    if min_term in min_terms:
                        popped = True
                        min_terms.pop(min_terms.index(min_term))
                        # tricky but right direction / maybe weights if you change your opinion
                if popped:
                    self.prime_implicants.append(implicant)
                if not min_terms:  # n min_terms left
                    return


test = QuineMcCluskey((0, 1, 2))
# print(test.implicants)
print(test.simple_expression)
#  print(test.num_of_ones_table)
"""print(test.size_implicants_table)
print(test.final_implicants)
print(test.implicants)
print(test.simple_expression) """
"""for i in test.size_implicants_table:
    print(i)"""

