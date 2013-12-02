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

n = 16
@memoize
def r(v1, v2):
  return random.randint(0, 1000)
def f(i, j, k):
  assert ((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n))
  if (k == 0):
    return r(i, j)
  else:
    return (f(i, j, (k - 1)) + f(i, (k - 1), (k - 1))*f((k - 1), j, (k - 1)))
def b1(i, j, k, n, r, s, r_0, r_1, s_0, s_1, s_2):
  assert (((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n)) and (((i < n/2) and (j < n/2)) and (k <= n/2)))
  if (n < 4):
    return b(i, j, k, n, r, s, r_0, r_1, s_0, s_1, s_2)
  elif (((i < n/4) and (j < n/4)) and (k < n/4)):
    return b1(i, j, k, n/2, r, s, r_0, r_1, s_0, s_1, s_2)
  elif (((i < n/4) and (j < n/4)) and (not (k < n/4))):
    return d(i, j, (k - n/4), n/2, (lambda i110, j111: d(i110, j111, n/4, n, r, s, (lambda _v26, _v27, _v28: b1(_v26, _v27, _v28, n, r, s, r_0, r_1, s_0, s_1, s_2)), r_0, r_1, s_0, s_1, s_2, 0, 0, 0)), s, (lambda _v107, _v108, _v109: b1(_v107, _v108, _v109, n, r, s, r_0, r_1, s_0, s_1, s_2)), 0, 0, s_0, (n*1/4 + s_1), (n*1/4 + s_2), n*1/4, 0, n*1/4)
  elif (((i < n/4) and (not (j < n/4))) and (k < n/4)):
    return b1(i, (j - n/4), k, n/2, r, s, r_0, (n*1/4 + r_1), s_0, s_1, s_2)
  elif (((i < n/4) and (not (j < n/4))) and (not (k < n/4))):
    return d(i, (j - n/4), (k - n/4), n/2, (lambda i127, j128: d(i127, j128, n/4, n, r, s, (lambda _v26, _v27, _v28: b1(_v26, _v27, _v28, n, r, s, r_0, r_1, s_0, s_1, s_2)), r_0, r_1, s_0, s_1, s_2, 0, 0, 0)), s, (lambda _v124, _v125, _v126: b1(_v124, _v125, _v126, n, r, s, r_0, r_1, s_0, s_1, s_2)), 0, n*1/4, s_0, (n*1/4 + s_1), (n*1/4 + s_2), n*1/4, n*1/4, n*1/4)
  elif (((not (i < n/4)) and (j < n/4)) and (k < n/4)):
    return d((i - n/4), j, k, n/2, r, s, (lambda _v26, _v27, _v28: b1(_v26, _v27, _v28, n, r, s, r_0, r_1, s_0, s_1, s_2)), (n*1/4 + r_0), r_1, (n*1/4 + s_0), s_1, s_2, 0, 0, 0)
  elif (((not (i < n/4)) and (j < n/4)) and (not (k < n/4))):
    return b1((i - n/4), j, (k - n/4), n/2, (lambda i82, j83: b1(i82, j83, n/4, n, r, s, r_0, r_1, s_0, s_1, s_2)), s, n*1/4, 0, (n*1/4 + s_0), (n*1/4 + s_1), (n*1/4 + s_2))
  elif (((not (i < n/4)) and (not (j < n/4))) and (k < n/4)):
    return d((i - n/4), (j - n/4), k, n/2, r, s, (lambda _v68, _v69, _v70: b1(_v68, _v69, _v70, n, r, s, r_0, r_1, s_0, s_1, s_2)), (n*1/4 + r_0), (n*1/4 + r_1), (n*1/4 + s_0), s_1, s_2, 0, n*1/4, 0)
  elif (((not (i < n/4)) and (not (j < n/4))) and (not (k < n/4))):
    return b1((i - n/4), (j - n/4), (k - n/4), n/2, (lambda i94, j95: b1(i94, j95, n/4, n, r, s, r_0, r_1, s_0, s_1, s_2)), s, n*1/4, n*1/4, (n*1/4 + s_0), (n*1/4 + s_1), (n*1/4 + s_2))
  else:
    return None
def d(i, j, k, n, r, s, t, r_0, r_1, s_0, s_1, s_2, t_0, t_1, t_2):
  assert (((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n)) and (((i < n/2) and (j < n/2)) and (k <= n/2)))
  if (k == 0):
    return r((i + r_0), (j + r_1))
  else:
    return (d(i, j, (k - 1), n, r, s, t, r_0, r_1, s_0, s_1, s_2, t_0, t_1, t_2) + s((i + s_0), ((k - 1) + s_1), ((k - 1) + s_2))*t(((k - 1) + t_0), (j + t_1), ((k - 1) + t_2)))
def c(i, j, k, n, r, s, r_0, r_1, s_0, s_1, s_2):
  assert (((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n)) and (((i < n/2) and (j < n/2)) and (k <= n/2)))
  if (k == 0):
    return r((i + r_0), (j + r_1))
  else:
    return (c(i, j, (k - 1), n, r, s, r_0, r_1, s_0, s_1, s_2) + c(i, (k - 1), (k - 1), n, r, s, r_0, r_1, s_0, s_1, s_2)*s(((k - 1) + s_0), (j + s_1), ((k - 1) + s_2)))
def a1(i, j, k, n, r, r_0, r_1):
  assert ((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n))
  if (n < 2):
    return a(i, j, k, n, r, r_0, r_1)
  elif (((i < n/2) and (j < n/2)) and (k <= n/2)):
    return a1(i, j, k, n/2, r, r_0, r_1)
  elif (((i < n/2) and (j < n/2)) and (not (k <= n/2))):
    return d(i, j, (k - n/2), n, (lambda i140, j141: a1(i140, j141, n/2, n, r, r_0, r_1)), (lambda _v239, _v240, _v241: a1(_v239, _v240, _v241, n, r, r_0, r_1)), (lambda _v242, _v243, _v244: a1(_v242, _v243, _v244, n, r, r_0, r_1)), 0, 0, 0, n*1/2, n*1/2, n*1/2, 0, n*1/2)
  elif (((i < n/2) and (not (j < n/2))) and (k <= n/2)):
    return b1(i, (j - n/2), k, n, r, (lambda i137, j138, k139: a1(i137, j138, k139, n, r, r_0, r_1)), r_0, (n*1/2 + r_1), 0, 0, 0)
  elif (((i < n/2) and (not (j < n/2))) and (not (k <= n/2))):
    return c(i, (j - n/2), (k - n/2), n, (lambda _v212, _v213: a1(_v212, _v213, n/2, n, r, r_0, r_1)), (lambda _v203, _v204, _v205: a1(_v203, _v204, _v205, n, r, r_0, r_1)), 0, n*1/2, n*1/2, n*1/2, n*1/2)
  elif (((not (i < n/2)) and (j < n/2)) and (k <= n/2)):
    return c((i - n/2), j, k, n, r, (lambda i137, j138, k139: a1(i137, j138, k139, n, r, r_0, r_1)), (n*1/2 + r_0), r_1, 0, 0, 0)
  elif (((not (i < n/2)) and (j < n/2)) and (not (k <= n/2))):
    return b1((i - n/2), j, (k - n/2), n, (lambda _v230, _v231: a1(_v230, _v231, n/2, n, r, r_0, r_1)), (lambda _v221, _v222, _v223: a1(_v221, _v222, _v223, n, r, r_0, r_1)), n*1/2, 0, n*1/2, n*1/2, n*1/2)
  elif (((not (i < n/2)) and (not (j < n/2))) and (k <= n/2)):
    return d((i - n/2), (j - n/2), k, n, r, (lambda _v173, _v174, _v175: a1(_v173, _v174, _v175, n, r, r_0, r_1)), (lambda _v176, _v177, _v178: a1(_v176, _v177, _v178, n, r, r_0, r_1)), (n*1/2 + r_0), (n*1/2 + r_1), n*1/2, 0, 0, 0, n*1/2, 0)
  elif (((not (i < n/2)) and (not (j < n/2))) and (not (k <= n/2))):
    return a1((i - n/2), (j - n/2), (k - n/2), n/2, (lambda _v195, _v196: a1(_v195, _v196, n/2, n, r, r_0, r_1)), n*1/2, n*1/2)
  else:
    return None
def a(i, j, k, n, r, r_0, r_1):
  assert ((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n))
  if (k == 0):
    return r((i + r_0), (j + r_1))
  else:
    return (a(i, j, (k - 1), n, r, r_0, r_1) + a(i, (k - 1), (k - 1), n, r, r_0, r_1)*a((k - 1), j, (k - 1), n, r, r_0, r_1))
def b(i, j, k, n, r, s, r_0, r_1, s_0, s_1, s_2):
  assert (((((((0 <= i) and (i < n)) and (0 <= j)) and (j < n)) and (0 <= k)) and (k <= n)) and (((i < n/2) and (j < n/2)) and (k <= n/2)))
  if (k == 0):
    return r((i + r_0), (j + r_1))
  else:
    return (b(i, j, (k - 1), n, r, s, r_0, r_1, s_0, s_1, s_2) + s((i + s_0), ((k - 1) + s_1), ((k - 1) + s_2))*b((k - 1), j, (k - 1), n, r, s, r_0, r_1, s_0, s_1, s_2))
