#!/usr/bin/python
class memoize(dict):
  def __init__(self, func):
    self.func = func
  def __call__(self, *args):
    return self[args]
  def __missing__(self, key):
    result = self[key] = self.func(*key)
    return result
plus = min
zero = 10000000000000000000000000000

import random
import sys
sys.setrecursionlimit(2 ** 16)

@memoize
def x(v1):
  return random.randint(0, 1000)
@memoize
def w(v1, v2, v3):
  return random.randint(0, 1000)
def d111(i, j, n, w, r, s, t):
  # assert (((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2)) and ((not (i < n/4)) and (not (j < n/4))))
  return d1((i - n/4), (j - n/4), n/2, (lambda _v251, _v252, _v253: w((_v251 + n/4), (_v252 + n/4), (_v253 + n/4))), (lambda i249, j250: d1(i249, j250, n/2, (lambda _v240, _v241, _v242: w((_v240 + n/4), _v241, (_v242 + n/4))), (lambda _v243, _v244: r((_v243 + n/4), (_v244 + n/4))), (lambda _v245, _v246: s((_v245 + n/4), _v246)), (lambda _v247, _v248: t(_v247, (_v248 + n/4))))), (lambda _v254, _v255: s((_v254 + n/4), (_v255 + n/4))), (lambda _v256, _v257: t((_v256 + n/4), (_v257 + n/4))))
def d101(i, j, n, w, r, s, t):
  # assert (((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2)) and ((i < n/4) and (not (j < n/4))))
  return d1(i, (j - n/4), n/2, (lambda _v224, _v225, _v226: w(_v224, (_v225 + n/4), (_v226 + n/4))), (lambda i222, j223: d1(i222, j223, n/2, (lambda _v215, _v216, _v217: w(_v215, _v216, (_v217 + n/4))), (lambda _v218, _v219: r(_v218, (_v219 + n/4))), s, (lambda _v220, _v221: t(_v220, (_v221 + n/4))))), (lambda _v227, _v228: s(_v227, (_v228 + n/4))), (lambda _v229, _v230: t((_v229 + n/4), (_v230 + n/4))))
def d110(i, j, n, w, r, s, t):
  # assert (((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2)) and ((not (i < n/4)) and (j < n/4)))
  return d1((i - n/4), j, n/2, (lambda _v199, _v200, _v201: w((_v199 + n/4), (_v200 + n/4), _v201)), (lambda i197, j198: d1(i197, j198, n/2, (lambda _v190, _v191, _v192: w((_v190 + n/4), _v191, _v192)), (lambda _v193, _v194: r((_v193 + n/4), _v194)), (lambda _v195, _v196: s((_v195 + n/4), _v196)), t)), (lambda _v202, _v203: s((_v202 + n/4), (_v203 + n/4))), (lambda _v204, _v205: t((_v204 + n/4), _v205)))
def d100(i, j, n, w, r, s, t):
  # assert (((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2)) and ((i < n/4) and (j < n/4)))
  return d1(i, j, n/2, w, (lambda i179, j180: d1(i179, j180, n/2, (lambda _v172, _v173, _v174: w(_v172, (_v173 + n/4), _v174)), r, (lambda _v175, _v176: s(_v175, (_v176 + n/4))), (lambda _v177, _v178: t((_v177 + n/4), _v178)))), s, t)
def d1(i, j, n, w, r, s, t):
  # assert ((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2))
  if (n < 4):
    return d(i, j, n, w, r, s, t)
  elif ((i < n/4) and (j < n/4)):
    return d100(i, j, n, w, r, s, t)
  elif ((i < n/4) and (not (j < n/4))):
    return d101(i, j, n, w, r, s, t)
  elif ((not (i < n/4)) and (j < n/4)):
    return d110(i, j, n, w, r, s, t)
  elif ((not (i < n/4)) and (not (j < n/4))):
    return d111(i, j, n, w, r, s, t)
  else:
    return None
def b101(i, j, n, w, r, s, t, w1):
  assert ((((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2)))) and ((i < n/4) and (not (j < (n/2 + n/4)))))
  return b1(i, (j - n/2), n/2, (lambda _v141, _v142, _v143: w(_v141, (_v142 + n/2), (_v143 + n/2))), (lambda i160, j161: d1(i160, (j161 + n/2), n/2, (lambda _v144, _v145, _v146: w1(_v144, (_v145 + n/4), _v146)), (lambda i154, j155: d1(i154, j155, n/2, (lambda _v147, _v148, _v149: w(_v147, (_v148 + n/2), _v149)), r, (lambda _v150, _v151: (lambda i72, j73: b1(i72, j73, n, w, r, s, t, w1))(_v150, (_v151 + n/2))), (lambda _v152, _v153: t((_v152 + n/2), _v153)))), (lambda _v156, _v157: s(_v156, (_v157 + n/4))), (lambda _v158, _v159: (lambda i72, j73: b1(i72, j73, n, w, r, s, t, w1))((_v158 + n/4), _v159)))), s, (lambda _v139, _v140: t((_v139 + n/2), (_v140 + n/2))), (lambda _v136, _v137, _v138: w1(_v136, _v137, (_v138 + n/2))))
def b111(i, j, n, w, r, s, t, w1):
  assert ((((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2)))) and ((not (i < n/4)) and (not (j < (n/2 + n/4)))))
  return b1((i - n/4), (j - n/2), n/2, (lambda _v109, _v110, _v111: w((_v109 + n/4), (_v110 + n/2), (_v111 + n/2))), (lambda i122, j123: d1((i122 + n/4), (j123 + n/2), n/2, (lambda _v115, _v116, _v117: w(_v115, (_v116 + n/2), _v117)), r, (lambda _v118, _v119: (lambda i72, j73: b1(i72, j73, n, w, r, s, t, w1))(_v118, (_v119 + n/2))), (lambda _v120, _v121: t((_v120 + n/2), _v121)))), (lambda _v105, _v106: s((_v105 + n/4), (_v106 + n/4))), (lambda _v107, _v108: t((_v107 + n/2), (_v108 + n/2))), (lambda _v112, _v113, _v114: w1((_v112 + n/4), (_v113 + n/4), (_v114 + n/2))))
def b100(i, j, n, w, r, s, t, w1):
  assert ((((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2)))) and ((i < n/4) and (j < (n/2 + n/4))))
  return b1(i, (j - n/4), n/2, (lambda _v76, _v77, _v78: w(_v76, (_v77 + n/4), (_v78 + n/4))), (lambda i93, j94: d1(i93, (j94 - n/4), n/2, (lambda _v84, _v85, _v86: w1(_v84, (_v85 + n/4), (_v86 + n/2))), (lambda _v87, _v88: r(_v87, (_v88 + n/2))), (lambda _v89, _v90: s(_v89, (_v90 + n/4))), (lambda _v91, _v92: (lambda i72, j73: b1(i72, j73, n, w, r, s, t, w1))((_v91 + n/4), (_v92 + n/2))))), s, (lambda _v82, _v83: t((_v82 + n/4), (_v83 + n/4))), (lambda _v79, _v80, _v81: w1(_v79, _v80, (_v81 + n/4))))
def b110(i, j, n, w, r, s, t, w1):
  assert ((((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2)))) and ((not (i < n/4)) and (j < (n/2 + n/4))))
  return b1((i - n/4), (j - n/4), n/2, (lambda _v52, _v53, _v54: w((_v52 + n/4), (_v53 + n/4), (_v54 + n/4))), (lambda _v62, _v63: r((_v62 + n/4), (_v63 + n/4))), (lambda _v58, _v59: s((_v58 + n/4), (_v59 + n/4))), (lambda _v60, _v61: t((_v60 + n/4), (_v61 + n/4))), (lambda _v55, _v56, _v57: w1((_v55 + n/4), (_v56 + n/4), (_v57 + n/4))))
def b1(i, j, n, w, r, s, t, w1):
  assert (((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2))))
  if (n < 4):
    return b0(i, j, n, w, r, s, t, w1)
  elif ((i < n/4) and (j < (n/2 + n/4))):
    return b100(i, j, n, w, r, s, t, w1)
  elif ((i < n/4) and (not (j < (n/2 + n/4)))):
    return b101(i, j, n, w, r, s, t, w1)
  elif ((not (i < n/4)) and (j < (n/2 + n/4))):
    return b110(i, j, n, w, r, s, t, w1)
  elif ((not (i < n/4)) and (not (j < (n/2 + n/4)))):
    return b111(i, j, n, w, r, s, t, w1)
  else:
    return None
def c111(i, j, n, w, r):
  assert (((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((not (i < n/2)) and (not (j < n/2))))
  return c1((i - n/2), (j - n/2), n/2, (lambda _v11, _v12, _v13: w((_v11 + n/2), (_v12 + n/2), (_v13 + n/2))), (lambda _v14, _v15: r((_v14 + n/2), (_v15 + n/2))))
def c100(i, j, n, w, r):
  assert (((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (j < n/2)))
  return c1(i, j, n/2, w, r)
def c1(i, j, n, w, r):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  if (n < 4):
    return c0(i, j, n, w, r)
  elif ((i < n/2) and (j < n/2)):
    return c100(i, j, n, w, r)
  elif ((i < n/2) and (not (j < n/2))):
    return b1(i, j, n, w, r, (lambda _v27, _v28: c100(_v27, _v28, n, w, r)), (lambda _v34, _v35: c111(_v34, _v35, n, w, r)), (lambda _v42, _v43, _v44: w(_v42, _v43, _v44)))
  elif ((not (i < n/2)) and (not (j < n/2))):
    return c111(i, j, n, w, r)
  else:
    return None
def r(i, j):
  assert True
  if (i == (j - 1)):
    return x(i)
  else:
    return zero
def d(i, j, n, w, r, s, t):
  # assert ((((0 <= i) and (i < n/2)) and (0 <= j)) and (j < n/2))
  return plus(reduce(plus, [((s(i, k) + t(k, j)) + w(i, k, j)) for k in range(0, n/2)], zero), r(i, j))
def b0(i, j, n, w, r, s, t, w1):
  assert (((((0 <= i) and (i < n)) and (i < j)) and (j < n)) and ((i < n/2) and (not (j < n/2))))
  return plus(reduce(plus, [((s(i, k1) + b0(k1, j, n, w, r, s, t, w1)) + w1(i, k1, j)) for k1 in range((i + 1), n/2)] + [((b0(i, k2, n, w, r, s, t, w1) + t(k2, j)) + w(i, k2, j)) for k2 in range(n/2, j)], zero), r(i, j))
def c0(i, j, n, w, r):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  return plus(reduce(plus, [((c0(i, k, n, w, r) + c0(k, j, n, w, r)) + w(i, k, j)) for k in range((i + 1), j)], zero), r(i, j))
def c(i, j):
  assert ((((0 <= i) and (i < n)) and (i < j)) and (j < n))
  if (i == (j - 1)):
    return x(i)
  else:
    return reduce(plus, [((c(i, k) + c(k, j)) + w(i, k, j)) for k in range((i + 1), j)], zero)
# c == (lambda i4, j5: c1(i4, j5, n, w, r))

n = 16
for i in range(0, n):
  for j in range(i+1, n):
    print i, j
    assert c(i, j) == c1(i, j, n, w, r)

