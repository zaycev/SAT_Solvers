#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Author: Vladimir Zaytsev <vzaytsev@isi.edu>

# Usage:
#       python igen.py 
#

import gc
import random
import multiprocessing



class WSProblem(object):
    """
    Raw WSP representation using relation matrix.
    """
    
    E = "e"
    F = "f"
    I = "i"
    
    def __init__(self, m, n, f, e, rel=None):
        random.seed()
        
        self.m = m
        self.n = n
        self.f = f
        self.e = e
        self.rel = rel

        if not self.rel:
            self.rel = []
            for i in xrange(m):
                self.rel.append([self.I] * m)
    
    @staticmethod
    def generate(m, n, f, e):
        p = WSProblem(m, n, f, e)
        
        for i in xrange(m):
            for j in xrange(i):
                rnd = random.randint(1, 100)
                
                if rnd <= f:
                    p.rel[i][j] = p.F
                    p.rel[j][i] = p.F
                elif f < rnd < f + e:
                    p.rel[i][j] = p.E
                    p.rel[j][i] = p.E
        
        return p
        
    def friends(self):
        pairs = []
        for i in xrange(self.m):
            for j in xrange(i):
                if self.rel[i][j] == self.F and i != j:
                    pairs.append((i, j))
        return pairs
                
    def enemies(self):
        pairs = []
        for i in xrange(self.m):
            for j in xrange(i):
                if self.rel[i][j] == self.E and i != j:
                    pairs.append((i, j))
        return pairs
        
    def guests(self):
        return xrange(self.m)
        
    def tables(self):
        return xrange(self.n)

    def pprint(self):
        for r in self.rel:
            print r



def __inc_mask(mask, ind, max_val):
    """
    Needed for generation all combinations in DNF2CNF transformation procedure.
    """
    if mask[ind] == max_val - 1:
        mask[ind] = 0
        __inc_mask(mask, ind - 1, max_val)
    else:
        mask[ind] += 1

def __gen_comb(sets, mask, mask_rank):
    """
    Generates all possible combinations length=len(sets) of elements of sets.
    """
    p = [None] * len(sets)
    for i in xrange(0, len(p)):
        p[i] = sets[i][mask[i]]
    __inc_mask(mask, len(mask) - 1, mask_rank)
    return p

def k_dnf_to_cnf(dnf):
    """
    Transforms DNF clauses of length k to CNF form.
    """
    mask = [0] * len(dnf)
    rank = len(dnf[0])
    for _ in xrange(rank ** rank):
        perm = __gen_comb(dnf, mask, rank)
        yield perm



def optim_cl(cl):
    """
    Optimizes disjunctive clause.
    """
    d = dict()
    new_cl = []
    for var, pos in cl:
        pos2 = d.get(var, -1)
        if pos2 == -1:
            d[var] = pos
            new_cl.append((var, pos))
        elif pos2 == pos:
            continue
        elif pos2 != pos:
            return True # (x or not(x)) found => always true
    return new_cl
    


def encode_cl(cl):
    """
    Encodes clause to make it able to be stored in a set.
    """
    scl = sorted(cl)
    encoded = [None] * (len(cl) * 3)
    for i in xrange(len(scl)):
        encoded[i * 3] = str(scl[i][0][0])
        encoded[i * 3 + 1] = str(scl[i][0][1])
        encoded[i * 3 + 2] = str(scl[i][1])
    return ",".join(encoded)


# cl = [((0, 1), 1), ((0, 0), 1), ((12, 1), 12)]
# 
# print encode_cl(cl)



def wsp_to_cnf(wsp, opt=True):
    """
    Encodes WSP problem to CNF form using the method described in Q1.
    
    Each literal represented as ((m, n), True), which means X_{m,n}
                              or ((m, n), False), which means not(X_{m,n})
    Clause is a list or tuple of such literals.
    CNF sentance is list of clauses.
    """
    
    tables = wsp.tables()
    guests = wsp.guests()
    friends = wsp.friends()
    enemies = wsp.enemies()
    
    full_cnf = []
    
    # (a) constraint
    for g in guests:
        dnf = []
        for t1 in tables:
            c = []
            for t2 in tables:
                var = (g, t2)
                pos = t1 == t2
                c.append((var, pos))
            dnf.append(c)
        cnf = k_dnf_to_cnf(dnf)
        full_cnf.extend(cnf)
        
    # (b) constraint
    for x, y in friends:
        dnf = []
        for t in tables:
            lit1 = ((x, t), True)
            lit2 = ((y, t), True)
            dnf.append([lit1, lit2])
        cnf = k_dnf_to_cnf(dnf)
        full_cnf.extend(cnf)
                
    # (c) constraint
    for x, y in enemies:
        cnf = []
        for t in tables:
            lit1 = ((x, t), False)
            lit2 = ((y, t), False)
            cnf.append([lit1, lit2])
        full_cnf.extend(cnf)

    if opt:
        # optimize clauses and remove all clauses which are always True
        opt = filter(lambda cl: cl != True, map(optim_cl, full_cnf))
        # remove dublicates
        cl_dic = dict()
        for cl in opt:
            k = encode_cl(cl)
            cl_dic[k] = cl
        opt_cnf = cl_dic.values()
        print "optimized %d => %d cls" % (len(full_cnf), len(opt_cnf))
        return opt_cnf
    return full_cnf
    
    
def gen_comb_pairs(clist, resolved=set()):
    """
    Produces all combinations (len=2) of clauses from clauses list <clist>.
    Does not produces combinations if they are in <resolved> set.
    Populates <resolved> set to reduce number of computations.
    """

    pairs = []
    for i in xrange(len(clist)):
        for j in xrange(len(clist)):
            if i != j and (i, j) not in resolved:
                resolved.add((i, j))
                pairs.append(((i, clist[i]), (j, clist[j])))
    return pairs
    

    
def pl_resolve(cl1, cl2):
    """
    Computes resolvet of two clauses or return False if they do not have
    complimentary literals.
    """

    cl1 = cl1[:]
    cl2 = cl2[:]
    d = dict()
    for i, (var, pos) in enumerate(cl1):
        d[var] = (pos, i)
    for i2, (var, pos2) in enumerate(cl2):
        pos1, i1 = d.get(var, (-1, None))
        if pos1 == -1:
            continue
        elif pos1 == pos2:
            continue
        else:
            cl1.pop(i1)
            cl2.pop(i2)
            resolvet = cl1 + cl2
            rresolvet = optim_cl(resolvet)
            # print "%r => %r" % (resolvet, rresolvet)
            return rresolvet
    return False # no complimentary literals found
    

def pl_resolution(cnf):
    """
    PL Resolution.
    """
    
    resolved = set()
    cl_set = set([encode_cl(cl) for cl in cnf])
    
    # print cnf
    # print cl_set
    
    while True:
        pairs = gen_comb_pairs(cnf, resolved)
        compl_pairs = False
        for (i1, cl1), (i2, cl2) in pairs:
            # if (i1, i2) not in resolved:
            resolved.add((i1, i2))
            resolvet = pl_resolve(cl1, cl2)
            if resolvet == True or resolvet == False:
                continue
            elif resolvet == []: # EMPTY_CLAUSE found
                return False
            else:
                r_enc = encode_cl(resolvet)
                if r_enc not in cl_set:
                    cnf.append(resolvet)
                    cl_set.add(r_enc)
                    compl_pairs = True                    

        # No new clauses produced (NEW in CLAUSES)
        if not compl_pairs:
            return True


# print pl_resolve(cl1, cl2)
# print cl1, cl2
# print pl_resolve(cl1, cl2)
# print cl1, cl2
# print pl_resolve(cl1, cl2)
# print cl1, cl2            

# cl1 = [("x", 1), ("y", 1), ("z", 0)]
# cl2 = [("x", 0), ("y", 0), ("z", 0)]


# print cl1, cl2            
# print pl_resolution([cl1, cl2])
# print cl1, cl2            

# def eval_cl(cl, assgn):
#     evl_cl = []
#     for var, pos in cl:
#         evl_cl.append(assgn[var] if pos else not assgn[var])
#     return any(evl_cl)


def eval_cl(cl, assgn):
    """
    Evaluates value of a clause using a model <assgn>.
    """
    for var, pos in cl:
        if (assgn[var] if pos else not assgn[var]):
            return True
    return False
    

# cl1 = [("x", True), ("y", True)]
# cl2 = [("x", False), ("y", True)]
# cl3 = [("x", True), ("y", False)]
# cl4 = [("x", False), ("y", False)]
# 
# assgn = {
#     "x": True,
#     "y": False,
# }
# 
# print eval_cl(cl1, assgn)
# print eval_cl(cl2, assgn)
# print eval_cl(cl3, assgn)
# print eval_cl(cl4, assgn)


def walk_sat(cnf, p=50, max_flips=1000):
    """
    Walk SAT.
    """
    
    sym_index = dict()
    sym_assgn = dict()
    tr_cls = set()
    fl_cls = set()
    
    # create inverted index <sym_index> for fast searching clauses by literals
    for cl in cnf:
        for var, pos in cl:
            cl_set = sym_index.get(var)
            if not cl_set:
                cl_set = set([tuple(cl)])
                sym_index[var] = cl_set
            else:
                cl_set.add(tuple(cl))
    
    # perform initial assigment
    for s in sym_index.iterkeys():
        sym_assgn[s] = random.choice((True, False))
    
    # create sets of TRUE and FALSE clauses
    for cl in cnf:
        val = eval_cl(cl, sym_assgn)
        if val:
            tr_cls.add(tuple(cl))
        else:
            fl_cls.add(tuple(cl))
    
    if len(fl_cls) == 0:
        return True
    
    # Body of algorithm
    for flip in xrange(max_flips):
        
        # Pick a random false clause
        cl = random.sample(fl_cls, 1)[0]
        dice = random.randint(1, 100)
        
        if dice <= p: # Perform random strategy
            s = random.choice(cl)        
            prev = sym_assgn[s[0]]
            sym_assgn[s[0]] = not prev
                    
            for cl in sym_index[s[0]]:
                val = eval_cl(cl, sym_assgn)
            
                if val == False and cl in tr_cls:
                    tr_cls.remove(cl)
                    fl_cls.add(cl)
                elif val == True and cl in fl_cls:
                    fl_cls.remove(cl)
                    tr_cls.add(cl)
        
        else: # Perform greedy strategy
            max_trs = -len(cnf)
            opt_chs = None
            
            # Lineary search an optimal choice
            for s, s_cls in sym_index.iteritems():
                
                trs = 0
                
                # print s
                # print sym_assgn
                
                prev = sym_assgn[s]
                sym_assgn[s] = not prev
                
                for cl in s_cls:
                    if eval_cl(cl, sym_assgn):
                        trs += 1
                    else:
                        trs -= 1
                        
                sym_assgn[s] = prev
                        
                if trs > max_trs:
                    max_trs = trs
                    opt_chs = s
            
            # flip optimal choice
            prev = sym_assgn[opt_chs]
            sym_assgn[opt_chs] = not prev
            
            # replace changed clauses
            for cl in sym_index[opt_chs]:
                val = eval_cl(cl, sym_assgn)
                if val == False and cl in tr_cls:
                    tr_cls.remove(cl)
                    fl_cls.add(cl)
                elif val == True and cl in fl_cls:
                    fl_cls.remove(cl)
                    tr_cls.add(cl)
            
        
        # all clauses are True => satisfiable
        if len(fl_cls) == 0:
            return True, flip
    
    # no model found => unsatisfiable
    return False, max_flips

# 
# def l1(p):
#     return walk_sat(p, 50, 100)
# def l2(p):
#     return walk_sat(p, 50, 500)
# def l3(p):
#     return walk_sat(p, 50, 1000)

def clsm_ratio(cnf):
    sm_set = set()
    cl_set = set()
    for cl in cnf:
        cl_set.add(encode_cl(cl))
        for var, _ in cl:
            sm_set.add(var)
    return float(len(cl_set)) / float(len(sm_set))


def main():
    
    """
    wsp = WSProblem(3, 2, 0, 0, rel=
        [
            ["i", "e", "e"],
            ["e", "i", "e"],
            ["e", "e", "i"],
        ]
    )
    
    for x in xrange(0, 100):
        wsp = WSProblem.generate(42, 6, 2, 2)    
        cnf = wsp_to_cnf(wsp, opt=True)
    
        print walk_sat(cnf)
        
        gc.collect()
    
    return
    """

    # TASK 6
    
    # M, N cases
    cases = [
        (16, 2),
        (24, 3),
        (32, 4),
        (40, 5),
        (48, 6),
    ]
    pool = multiprocessing.Pool(processes=12)
    
    
    for m, n in cases:
        satisfiable = 0
        total_iters = 0
        cs_ratio = 0.0
        problems_n = 0
        while True:
            
            gc.collect()
            
            raw_problems = [WSProblem.generate(m, n, 2, 2) for _ in xrange(20) ]
            problems = pool.map(wsp_to_cnf, raw_problems)
            results = pool.map(walk_sat, problems)
                        
            problems_n += len(problems)
            for p in problems:
                cs_ratio += clsm_ratio(p)
            
            gc.collect()            
            results = pool.map(walk_sat, problems)
            
            for r in results:
                if r[0]:
                    satisfiable += 1
                    total_iters += r[1]                    

            if satisfiable >= satisfiable:
                print "%d, %d, %d, %f" % \
                    (m, n, float(total_iters) / float(satisfiable), cs_ratio / problems_n)
                break

    

if __name__ == "__main__":
    main()