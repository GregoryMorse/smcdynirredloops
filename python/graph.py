def succ_to_pred(succ):
  pred = {x: set() for x in succ}
  for x in succ:
    for y in succ[x]:
      pred[y].add(x)
  return pred

def topo_kahn(g, randomize=False):
  if randomize: import random
  topo, S, k = [], [], 0
  inc = {u: 0 for u in g}
  for u in g:
    for v in g[u]: inc[v] += 1
  for u in g:
    if inc[u] == 0: S.append(u)
  while len(S) != 0:
    u = S.pop(0 if not randomize else random.randint(0, len(S)-1)); k += 1
    topo.append(u)
    for v in g[u]:
      inc[v] -= 1
      if inc[v] == 0: S.append(v)
  if k < len(g): raise ValueError
  return topo
  
def topo_kahn_levels(g):
  levels, topo, S, k = [set(), set()], [], [], 0
  inc = {u: 0 for u in g}
  for u in g:
    for v in g[u]: inc[v] += 1
  curlvl = 0
  for u in g:
    if inc[u] == 0: levels[curlvl].add(u); S.append(u)
  while len(S) != 0:
    u = S.pop(); k += 1
    if not u in levels[curlvl]: curlvl += 1; levels.append(set())
    topo.append(u)
    for v in g[u]:
      inc[v] -= 1
      if inc[v] == 0: levels[curlvl+1].add(u); S.append(v)
  if k < len(g): raise ValueError
  return topo, levels
