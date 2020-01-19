def default(e, default, f, *rest):
    try:
        return f(*rest)
    except e:
        return default

def idfun(x): return x
def nonempty(x): return len(x) > 0
def is_singleton(x) : return len(x) == 1
def first(xs): return xs[0]
def second(xs): return xs[1]
def comp(*funcs):
    comp2 = lambda f, g: lambda x: f(g(x))
    return reduce(comp2, funcs, idfun)

def evensplit(it):
    if isinstance(it, list): it = iter(it)

    try:
        for elem in it:
            yield (elem, next(it))
    except StopIteration:
        return

maplist = lambda f, x: list(map(f, x))

val = 0
def gensym():
    global val
    val += 1
    return str(val)