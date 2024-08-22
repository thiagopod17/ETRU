#Todas as funções abaixo foram desenvolvidas com base nos artigos:
#[1] Katherine Jarvis, M. N. (2015). Etru: Ntru over the eisenstein integers. Designs, Codes and Cryptography, 74:219–242.
#[2] Monica Nevins, Camelia KarimianPour, A. M. (2010). Ntru over rings beyond z. Designs,Codes and Cryptography, 56:65–78
#[3] Donald Ervin Knuth. (1997). The Art of Computer Programming, volume 2 (3rd ed.): seminumerical algorithms. Addison-Wesley

##DEFININDO O ANEL Z[ω].
# Definindo Z[ω] que contém uma raiz cúbica primitiva da unidade ω^3=1.
K.<w> = CyclotomicField(3)
OK = K.ring_of_integers()   # Obtendo o anel de inteiros

# Definindo elementos básicos
OK0 = OK([0,0]) 
OK1 = OK([1,0])
OKw = OK([0,1])
OKw2 = OK([-1,-1])


# DEFININDO UM POLINÔMIO NO ANEL Z[ω][x] e Z[ω][x]/(x^n-1)
n = 50
Z.<x> = PolynomialRing(OK)  # Z[ω][x]
R = Z.quotient(x^n - 1)     # Z[ω][x]/(x^n-1)


def a_modb(a, b, return_qr = 0):
    #DESCRIPTION: Faz a redução modular de a mod b: a = q * b + r
    #INPUT: Elementos a, b em Z[ω] com b ≠ 0 
    #OUTPUT: Para return_qr = 0: r em Z[ω]
    #        Para return_qr = 1: q e r em Z[ω]
    N = (b*OK1).norm(); 
    u = a*b.conjugate()
    bu = u.imag() * 2  / sqrt(3)
    au = u.real() + bu / 2

    qa, ra = divmod(ZZ(au) ,ZZ(N))
    qb, rb = divmod(ZZ(bu) ,ZZ(N))
    
    if(ra > N/2): #Checar se precisa "centralizar"
        qa = qa + 1
    if(rb > N/2):
        qb = qb + 1
    q =  qa + qb * OKw 
    r =  a - q*b
    if(return_qr):
        return q,r
    else: 
        return r

def ax_modb(ax, b, return_qr = 0):
    #DESCRIPTION: Faz a redução modular de um polinômio em Z[ω][x] ou em Z[ω][x]/(x^n-1). 
    #             tal que ax = qx * b + rx
    
    #INPUT1: ax em Z[ω][x] e b em Z[ω], b ≠ 0
    #OUTPUT1: Para return_qr = 0: Retorna o polinômio rx em Z[ω][x]
    #         Para return_qr = 1: Retorna os polinômios qx e rx em Z[ω][x]
    
    #INPUT2: ax em Z[ω][x]/(x^n-1) e b em Z[ω], b ≠ 0
    #OUTPUT2: Para return_qr = 0: Retorna o polinômio rx em Z[ω][x]/(x^n-1)
    #         Para return_qr = 1: Retorna os polinômios qx e rx em Z[ω][x]/(x^n-1)
    
    isTypeR = (type(ax) == type(R.random_element()))
    if(isTypeR):
        degree = ax.lift().degree()
    else:
        degree = ax.degree()
    quoc = list()
    rmodq = list()
    for i in range(degree + 1):
        qr = a_modb(ax[i], b, 1)
        quoc.append(qr[0])
        rmodq.append(qr[1])
    if(return_qr):
        if(isTypeR):
            return R(quoc), R(rmodq)
        else:
            return Z(quoc), Z(rmodq)
    else:
        if(isTypeR):
            return R(rmodq)
        else:
            return Z(rmodq) 

def OK_random_non_zero(deg = 10):
    #OUTPUT: elemento nao nulo em Z[ω] de tamanho máximo deg
    b = OK0
    while(b == 0):
        b = OK.random_element(deg) 
    return b

def RrandomPoly(deg):
    #DESCRIPTION: Gera um polinômio aleatório em Z[ω][x] e passa ao quociente de (x^n-1)
    #INPUT: Grau do polinômio em Z[ω][x]
    #OUTPUT: Polinômio aleatório em Z[ω][x]/(x^n-1)
    return R(Z.random_element(deg))

def RrandomPolyModb(b, deg = 10):
    #DESCRIPTION: Gera um polinômio aleatório em Z[ω][x]/(x^n-1) e passa ao quociente de b
    #INPUT: b em Z[ω], b ≠ 0.
    #OUTPUT: Um polinômio aletório fx em Z[ω][x]/(x^n-1)
    p = RrandomPoly(deg)
    return ax_modb(p, b, 0)

def ZrandomPolyModb(b, deg = 10):
    #DESCRIPTION: Gera um polinômio aleatório em Z[ω][x] e passa ao quociente de b
    #INPUT: b em Z[ω], b ≠ 0.
    #OUTPUT: Um polinômio aletório fx em Z[ω][x]
    p = Z.random_element(deg)
    return ax_modb(p, b, 0)

def gcd(a,b):
    #DESCRIPTION: Calcula o MDC de dois elementos 
    #INPUT: Elementos a, b em Z[ω] com b ≠ 0.
    #OUTPUT: Retorna o MDC de a e b em Z[ω]
    if( b == OK0):
        return a
    else: 
        return gcd(b, a_modb(a, b, 0))
  
def extendedEuclidean(a, b):
    #DESCRIPTION: Aplica o Algoritmo de Euclides Estendido para achar elementos 
    #             s, t, r tal que s * a + t * b = r
    #INPUT: Elementos a, b em Z[ω]
    #OUTPUT: Retorna elementos s, t, r em Z[ω]
    r0, s0, t0 = a, OK1, OK0
    r1, s1, t1 = b, OK0, OK1
    
    while r1 != OK0:
        q, rnext = a_modb(r0, r1, 1)
        snext = s0 - q * s1
        tnext = t0 - q * t1
        
        r0, r1 = r1, rnext
        s0, s1 = s1, snext
        t0, t1 = t1, tnext
    
    return s0, t0, r0


def a_invZb(a,b):
    #DESCRIPTION: Calcula o inverso de a em Z[w]/<b>
    #INPUT: Elementos a, b em Z[ω], tal que a mod b ≠ 0 e b é primo em Z[w]
    #OUTPUT: Retorna um elemento c de Z[ω]/<b> tal que a*c = 1 mod b.
    s, t, r = extendedEuclidean(a, b)
    qqs, rrs = a_modb(s,r,1)
    qqt, rrt = a_modb(t,r,1)
    if a_modb(a, b) == OK0:
        raise ValueError(f"\n a mod b = 0  \n a = {a} \n b = {b}")
    if rrs != OK0 or rrt != OK0:
        raise ValueError("b is not a prime number in Z[w]",b) 
    else:
        return a_modb(qqs, b)

def PseudoDivisionPoly(u,v):
    #DESCRIPTION: Faz a pseudo divisão de polinômios, isto é, obter polinômios q, r em Z[ω][x]
    #             tal que vlp^{m-n+1} * u = q * v + r com deg(r) < n
    #             onde m = deg(u) e n = deg(v) e vlp é o coeficiente de maior grau de v.
    
    #INPUT: u, v em Z[ω][x] com v != 0 e deg(u) >= deg(v).
    #OUTPUT: q, r em  Z[ω][x]
    
    if( not( (u in Z) & (v in Z) ) ):
        raise ValueError("u and v must be in Z = PolynomialRing(OK,'x')")

    m = u.degree()
    u = u.list()
    n = v.degree()
    q = [1]*(max(0,m-n+1))
    if( m < n):
        raise ValueError("Error in pseudoDivision Poly, m < n entries are:", u, v)
        
    for k in reversed(range(0,m-n+1)):
        q[k] = u[n+k] * (v[n]**k)
        for j in reversed(range(0,n+k)):
            if((j-k) >= 0):
                u[j] = v[n] * u[j] - u[n+k] * v[j-k]
            else:
                u[j] = v[n] * u[j]
    r = [1]*(max(0,n))
    for i in range(0,max(0,n)):
        r[i] = u[i]
    return Z(q),Z(r)

def PseudoDivisionPoly_modb(u,v,b):
    #DESCRIPTION: Faz a pseudo divisão de polinômios modulo um elemento b de Z[ω], isto é, 
    #             obter polinômios q, r em Z[ω][x]/<b> tal que (vlp^{m-n+1} * u = q * v + r) mod b,  com deg(r) < n
    #             onde m = deg(u) e n = deg(v) e vlp é o coeficiente de maior grau de v.
    
    #INPUT: u, v em Z[ω][x] com v != 0 e deg(u) >= deg(v), b em Z[ω] 
    #OUTPUT: q, r em  Z[ω][x] / <b>
    
    if( not( (u in Z) & (v in Z) ) ):
        raise ValueError("u and v must be in Z = PolynomialRing(OK,'x')")

    m = u.degree()
    u = u.list()
    n = v.degree()
    q = [1]*(max(0,m-n+1)) 
    if( m < n):
        raise ValueError("Error in pseudoDivision Poly, m < n entries are:", u, v)
        
    for k in reversed(range(0,m-n+1)):
        vnk = 1
        for l in range(k):
            vnk *= v[n]
            vnk = a_modb(vnk,b)
        q[k] = a_modb(u[n+k] * vnk ,b)
        for j in reversed(range(0,n+k)):
            if( (j-k) >= 0):
                u[j] = a_modb(v[n] * u[j] - u[n+k] * v[j-k],b)
            else:
                u[j] = a_modb(v[n] * u[j],b)
    r = [1]*(max(0,n))
    for i in range(0,max(0,n)):
        r[i] = u[i]
    return Z(q),Z(r)

def DivisionPoly_modb(u,v,b):
    #DESCRIPTION: Faz a divisão de polinômios módulo um elemento b primo de Z[ω], isto é, obter polinômios 
    #             q, r em Z[ω][x]/<b> tal que (u = q * v + r) mod b com deg(r) < deg(v).
    
    #INPUT: u e v em Z[ω][x], v != 0, b primo em z[w] e deg(u) >= deg(v).
    #OUTPUT: q, r em  Z[ω][x]/<b>
    
    # check if polynomials are in Z
    if( not( (u in Z) & (v in Z) ) ):
        raise ValueError("u and v must be in Z = PolynomialRing(OK,'x')")
    
    u = ax_modb(u, b)
    v = ax_modb(v, b)

    m = u.degree()
    n = v.degree()
    if( m < n):
        return 0,u
    
    q, r = PseudoDivisionPoly_modb(u,v,b)
    vlp = v[v.degree()]
    vleadPower = 1
    for i in range(u.degree()-v.degree()+1):
        vleadPower *= vlp
        vleadPower = a_modb(vleadPower,b)
    vleadPowerInv = a_invZb(vleadPower , b) 
    
    q = ax_modb( vleadPowerInv * ax_modb(q,b), b )
    r = ax_modb( vleadPowerInv * ax_modb(r,b), b )

    return q,r

def gcd_Zb(u,v,b):
    #DESCRIPTION: Calcula o MDC de dois polinomios em Z[ω][x]/<b>
    #INPUT: Elementos u, v em Z[ω][x] e b ≠ 0, primo em Z[ω] .
    #OUTPUT: Retorna o MDC de u e v em Z[ω][x]/<b>
    if( v == 0):
        return u
    else:
        q,r = DivisionPoly_modb(u,v,b)
        return gcd_Zb(v,r,b)
    
#Algoritmo de Euclides Estendido para polinômios em Z[w]/<b>
def ExtendedEuclideanPoly_modb(f,g,b):
    #DESCRIPTION: Aplica o Algoritmo de Euclides Estendido para achar polinômios
    #             s, t, r tal que (s * f + t * g == r) mod b, onde r = gcd(f,g) em Z[ω][x]/<b>
    #INPUT: Polinomios f e g em Z[ω][x] com deg(f) >= deg(g)
    #OUTPUT: Retorna elementos s, t, r em Z[ω][x]/<b>
  
    f = ax_modb(f,b)
    g = ax_modb(g,b)
    
    fdeg = f.degree()
    gdeg = g.degree()
    if( fdeg < gdeg):
        raise ValueError("fdeg < gdeg")
    
    r0 = f
    s0 = Z(a_modb(OK1,b))
    t0 = Z(a_modb(OK0,b))
    r1 = g
    s1 = Z(a_modb(OK0,b))
    t1 = Z(a_modb(OK1,b))
    i = 1
    ri = r1 
    rnext = r1
    rprev = r0
    sprev = s0
    si = s1
    tprev = t0
    ti = t1
    while (ri != Z(a_modb(OK0,b)) ):
        qi, rnext = DivisionPoly_modb(rprev,ri,b) 
        snext = ax_modb(sprev - qi * si,b)
        tnext = ax_modb(tprev - qi * ti,b)
        
        i += 1
        rprev, ri = ri, rnext
        sprev, si = si, snext
        tprev, ti = ti, tnext

        
        rileadPower = ri[ri.degree()]^(rprev.degree()-ri.degree()+1)  
        if(ri == Z(a_modb(OK0,b))):
            return ax_modb(sprev,b), ax_modb(tprev,b), ax_modb(rprev, b)
        
def inv_poly_modb(f,g,b):
    #DESCRIPTION: Calcula o inverso de um polinômio g em Z[w][x]/(x^n-1) mod b
    #INPUT: Polinômio f, g em Z[ω][x], tal que f mod g ≠ 0, deg(f) >= deg(g) e b é primo em Z[w]
    #OUTPUT: Retorna um polinômio h de Z[w][x]/(x^n-1) mod b tal que g*h = 1 mod f mod b.
    s,t,r = ExtendedEuclideanPoly_modb(f,g,b)
    if r == OK1:
        return t
    else:
        qqs,rrs = DivisionPoly_modb(s,r,b) 
        qqt,rrt = DivisionPoly_modb(t,r,b) 
        if rrs == 0 and rrt == 0:
            return qqt
        else: 
            raise ValueError(f"Polinômio não é invertível em Z[w][x]/(x^n-1) mod {b}")    

import random
def mult_prox_de_3(n,r):
    # Calcula o próximo múltiplo de 3 de n/r
    N_int = int(r*n)
    N_frac = r*n - N_int
    mi = (N_int // 3) * 3  
    if N_frac > 1.5:
        return mi + 3
    else:
        return mi

def randomPolyinLg(n,p,q,r):
    #DESCRIPTION: Gera um polinômio aleatório em Lg subconjuto de Z[ω][x]/(x^n-1)
    #INPUT: Parâmetros interos positivos n,p,q,r do ETRU
    #OUTPUT: Um polinômio aletório f(x) em Lg 
    R = Z.quotient(x^n - 1)
    mu_3 = [OK1, OKw, OKw2]
    s = mult_prox_de_3(n,r)
    fts = []
    coef_poly = []
    for i in range(s/3):
        ft = random.choice([-1, 1])
        fts.append(ft)
    for i in fts:
        coef_poly += [i * elemento for elemento in mu_3]
    coef_poly += (n-s)*[0]
    j = list(range(n))
    random.shuffle(j)
    for l in sorted(j[:n-s]):
        for i in range(len(coef_poly) - 1, l, -1):
            coef_poly[i] = coef_poly[i - 1] 
        coef_poly[l] = 0
    return Z(list(reversed(coef_poly)))

def randomPolyinLf(n,p,q,r):
    #DESCRIPTION: Gera um polinômio aleatório em Lf subconjuto de Z[ω][x]/(x^n-1)
    #INPUT: Parâmetros interos positivos n,p,q,r do ETRU
    #OUTPUT: Um polinômio aletório f(x) em Lf 
    R = Z.quotient(x^n - 1) 
    mu_6 = [OK1, OKw, OKw2, -OK1, -OKw, -OKw2]
    t = round(r*n)
    coef_poly = []
    for i in range(0,t):
        coef_poly.append(mu_6[random.randint(0, 5)])
    coef_poly += (n-t)*[0]
    random.shuffle(coef_poly)
    f = Z(coef_poly)
    erros = 1
    try: 
        qq = x^n-1
        Fp = inv_poly_modb(qq,f,p)
        Fq = inv_poly_modb(qq,f,q)
        #print("Nº de polinômios f testados: ",erros)
        return f, Fp, Fq, erros
    except Exception as e:
        erros += 1
        return randomPolyinLf(n,p,q,r)
    
def key_gen(n,p,q,r, return_phi = 0):
    #DESCRIPTION: Gera as chaves privada e pública do ETRU. Também pode ser usada para gerar polinômios
    #             aleatórios usados na criptografia de mensagens
    
    #INPUT:  Parâmetros interos positivos n,p,q,r do ETRU
    #OUTPUT: Para return_phi = 0: Retorna polinômios [f, Fp h] em Z[ω][x]/(x^n-1) tal que
    #                             f, Fp = chave privada e h = chave pública 
    #        Para return_phi = 1: Retorna um polinômio aleatório em Z[ω][x]/(x^n-1) mod q (usado na cifração)
    if(return_phi):
        return randomPolyinLg(n,p,q,r)
    else:
        R = Z.quotient(x^n - 1)
        f, Fp, Fq, num_f_test = randomPolyinLf(n,p,q,r)
        g = randomPolyinLg(n,p,q,r)
        R = Z.quotient(x^n - 1)
        h = Z(R(Fq * g).list())
        h = ax_modb(Z(R(Fq * g).list()),q)
        return f, Fp, h, Fq, g

def encrypt(message,publickey):
    #DESCRIPTION: Faz a criptogria de uma mensagem.
    #INPUT: message = polinômio em Z[ω][x]/(x^n-1) mod p, publickey = polinômio em Z[ω][x]/(x^n-1) mod q
    #OUTPUT: Polinômio em Z[ω][x]/(x^n-1) mod q
    phi = key_gen(n,p,q,r,1)
    e = p*phi*publickey + m
    e = ax_modb(Z(R(e).list()),q)
    return e  

def decrypt(ciphertext,f, Fp):
    #DESCRIPTION: Faz a descriptogria de um ciphertext.
    #INPUT: ciphertext = polinômio em Z[ω][x]/(x^n-1) mod q, 
    #       f, Fp = chave privada, f = polinômio em Z[ω][x]/(x^n-1) como coeficientes sendo unidades em Z[ω]
    #                              Fp = inversa de f em Z[ω][x]/(x^n-1) mod p
    #OUTPUT: Polinômio em Z[ω][x]/(x^n-1) mod p
    a = f*ciphertext
    a = ax_modb(Z(R(a).list()),q)
    m = Fp*a
    m = ax_modb(Z(R(m).list()),p)
    return m

import pickle
def gen_key_database(n,p,q,qtd,t):
    #DESCRIPTION: Gera um arquivo pickle com um banco de dado de chaves.
    #INPUT: Parâmetros interos positivos n,p,q do ETRU, qtd = quantidade de chaves que serão geradas
    #OUTPUT: Gera um arquivo no diretórío com as chaves distribuída em uma lista na forma [f,Fp,h,Fq,g,n]
    #        onde f e Fp são as chaves privadas e h é chave pública.
    p = p*OK([1,0])
    q = q*OK([1,0])
    r = 2 / 3
    chaves = []
    R = Z.quotient(x^n - 1)
    for ii in range(qtd):
        f, Fp, h, Fq, g = key_gen(n,p,q,r)
        chaves.append([f,Fp,h,Fq,g,n])
    nome_arq =  "chaves_n_"+str(n)+"_num_"+str(t)+".pkl"
    with open(nome_arq,"wb") as chaves_etru:
        pickle.dump(chaves, chaves_etru)
    return  