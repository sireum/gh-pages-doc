// #Sireum #Logika
import org.sireum._

// Inductive definition of multiplication

@strictpure def mult_spec(m: Z, n: Z): Z = m match {
  case 0 => 0
  case k => mult_spec(k - 1, n) + n
}

// Induction rules

@pure def mult_spec_0(n: Z) {
  Contract(
    Ensures(mult_spec(0, n) == 0)
  )
}

@pure def mult_spec_step(m: Z, n: Z) {
  Contract(
    Requires(m > 0),
    Ensures(mult_spec(m, n) == mult_spec(m - 1, n) + n)
  )
  Deduce(|- (m != 0))
}

@pure def mult_rec(m: Z, n: Z): Z = {
  Contract(
    Requires(m >= 0),
    Ensures(Res == mult_spec(m, n))
  )
  if (m == 0) {
    return 0
  } else {
    return mult_rec(m - 1, n) + n
  }
}

def mult_it(m: Z, n: Z): Z = {
  Contract(
    Requires(m >= 0),
    Ensures(Res == mult_rec(m, n))
  )
  var i: Z = m
  var k: Z = 0
  Deduce(|- (k == mult_rec(m - i, n)))
  while (i > 0) {
    Invariant(
      Modifies(k, i),
      (i >= 0),
      (k == mult_rec(m - i, n))
    )
    Deduce(|- (k == mult_rec(m - i, n)))
    Deduce(|- (k + n == mult_rec(m - i, n) + n))
    Deduce(|- (k + n == mult_rec(m - i + 1, n)))
    Deduce(|- (k + n == mult_rec(m - (i - 1), n)))
    k = k + n
    Deduce(|- (k == mult_rec(m - (i - 1), n)))
    i = i - 1
    Deduce(|- (k == mult_rec(m - i, n)))
  }
  Deduce(|- (i <= 0))
  Deduce(|- (i == 0))
  Deduce(|- (k == mult_rec(m - i, n)))
  Deduce(|- (k == mult_rec(m - 0, n)))
  Deduce(|- (k == mult_rec(m, n)))
  return k
}

def mult_it_term(m: Z, n: Z): Z = {
  Contract(
    Requires(m >= 0),
    Ensures(Res == mult_rec(m, n))
  )
  var i: Z = m
  var k: Z = 0
  while (i > 0) {
    // decreases i
    Invariant(
      Modifies(k, i),
      (i >= 0),
      (k == mult_rec(m - i, n))
    )
    val measure_i_pre = i
    Deduce(|- (measure_i_pre >= 0))
    k = k + n
    i = i - 1
    val measure_i_post = i
    Deduce(|- (measure_i_post < measure_i_pre))
  }
  return k
}
