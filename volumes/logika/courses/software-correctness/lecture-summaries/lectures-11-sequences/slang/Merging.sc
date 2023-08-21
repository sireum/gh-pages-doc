// #Sireum #Logika

import org.sireum._

@pure def sorted(seq: ISZ[Z]): B = {
  Contract(
    Ensures(Res == All(1 until seq.size)(i => seq(i - 1) <= seq(i)))
  )
  if (seq.size == 0) {
    return true
  } else {
    var res: B = true;
    var k: Z = 1;
    while (k < seq.size) {
      Invariant(
        Modifies(k, res),
        k >= 1,
        k <= seq.size,
        res == All(1 until k)(i => seq(i - 1) <= seq(i)),
      )
      if (seq(k - 1) > seq(k)) {
        res = false
      }
      k = k + 1
    }
    return res
  }
}

@pure def contained(s: ISZ[Z], t: ISZ[Z]): B = {
  Contract(
    Ensures(Res == All(0 until s.size)(i => Exists(0 until t.size)(j => s(i) == t(j))))
  )
  var res = true
  var m: Z = 0
  while (m < s.size & res) {
    Invariant(
      Modifies (m, res),
      m >= 0,
      m <= s.size,
      res == All(0 until m)(i => Exists(0 until t.size)(j => s(i) == t(j)))
    )
    var n: Z = 0
    var found: B = false
    while (n < t.size) {
      Invariant(
        Modifies(n),
        n >= 0,
        n <= t.size,
        found == Exists(0 until n)(j => s(m) == t(j))
      )
      if (s(m) == t(n)) {
        found = true
      }
      n = n+1
    }
    Deduce(|-(found == Exists(0 until t.size)(j => s(m) == t(j))))
    if (!found) {
      Deduce(|-(!Exists(0 until t.size)(j => s(m) == t(j))))
      res = false
      Deduce(|-(res == All(0 until m+1)(i => Exists(0 until t.size)(j => s(i) == t(j)))))
    }
    Deduce(|-(res == All(0 until m+1)(i => Exists(0 until t.size)(j => s(i) == t(j)))))
    m = m+1
    Deduce(|-(res == All(0 until m)(i => Exists(0 until t.size)(j => s(i) == t(j)))))
  }
  return res
}

def merge(s: ISZ[Z], t: ISZ[Z]): ISZ[Z] = {
  Contract(
    Requires(sorted(s), sorted(t)),
    Ensures(contained(s, Res), contained(t, Res), sorted(Res))
  )
  var res = ISZ[Z]()
  var x = 0
  var y = 0
  while (x < s.size & y < t.size) {
    if (s(x) < t(y)) {
      res = res :+ s(x)
      x = x+1
    } else {
      res = res :+ t(y)
      y = y+1
    }
  }
  while (x < s.size) {
    res = res :+ s(x)
    x = x+1
  }
  while (y < t.size) {
    res = res :+ t(y)
    y = y+1
  }
  return res
}

def merge_with_proof(s: ISZ[Z], t: ISZ[Z]): ISZ[Z] = {
  Contract(
    Requires(sorted(s), sorted(t)),
    Ensures(contained(s, Res), contained(t, Res), sorted(Res))
  )
  var res = ISZ[Z]()
  var x = 0
  var y = 0
  var z = 0
  while (x < s.size & y < t.size) {
    Invariant(
      Modifies(x, y, res),
      x >= 0,
      x <= s.size,
      y >= 0,
      y <= t.size,
      z == res.size,
      All(0 until x)(i => Exists(0 until z)(j => s(i) == res(j))),
      All(0 until y)(i => Exists(0 until z)(j => t(i) == res(j))),
      (z == 0 | x == s.size) || res(z-1) <= s(x),
      (z == 0 | y == t.size) || res(z-1) <= t(y),
      All(1 until z)(i => res(i - 1) <= res(i))
    )
    if (s(x) < t(y)) {
      res = res :+ s(x)
      Deduce(|- (s(x) == res(z)))
      Deduce(|- (Exists(0 until z+1)(j => s(x) == res(j))))
      z = z + 1
      Deduce(|- (All(0 until x+1)(i => Exists(0 until z)(j => s(i) == res(j)))))
      x = x+1
    } else {
      res = res :+ t(y)
      Deduce(|- (t(y) == res(z)))
      Deduce(|- (Exists(0 until z+1)(j => t(y) == res(j))))
      Deduce(|- (All(1 until z+1)(i => res(i - 1) <= res(i))))
      z = z+1
      Deduce(|- (All(0 until y+1)(i => Exists(0 until z)(j => t(i) == res(j)))))
      y = y+1
    }
    Deduce(|- (All(0 until x)(i => Exists(0 until z)(j => s(i) == res(j)))))
    Deduce(|- (All(0 until y)(i => Exists(0 until z)(j => t(i) == res(j)))))
    //Deduce(|- (z == 0 || res(z-1) <= s(x)))
  }
  while (x < s.size) {
    Invariant(
      Modifies(x, res),
      x >= 0,
      x <= s.size,
      z == res.size,
      All(0 until x)(i => Exists(0 until z)(j => s(i) == res(j)))
    )
    res = res :+ s(x)
    Deduce(|-(s(x) == res(z)))
    Deduce(|-(Exists(0 until z + 1)(j => s(x) == res(j))))
    z = z+1
    Deduce(|- (All(0 until x+1)(i => Exists(0 until z)(j => s(i) == res(j)))))
    x = x+1
  }
  while (y < t.size) {
    Invariant(
      Modifies(y, res),
      y >= 0,
      y <= t.size,
      z == res.size,
      All(0 until y)(i => Exists(0 until z)(j => t(i) == res(j)))
    )
    res = res :+ t(y)
    Deduce(|-(t(y) == res(z)))
    Deduce(|-(Exists(0 until z + 1)(j => t(y) == res(j))))
    z = z+1
    Deduce(|- (All(0 until y+1)(i => Exists(0 until z)(j => t(i) == res(j)))))
    y = y+1
  }
  return res
}