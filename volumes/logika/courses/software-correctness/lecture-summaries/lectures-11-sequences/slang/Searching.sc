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

@pure def sorted_upper_bound(seq: ISZ[Z], i: Z, b: Z): B = {
  Contract(
    Requires(sorted(seq), 0 <= i, i < seq.size, seq(i) <= b),
    Ensures(Res == All(0 until i)(k => seq(k) <= b) & Res == true)
  )
  var j: Z = i
  while (j > 0) {
    Invariant(
      Modifies(j),
      0 <= j,
      j < seq.size,
      seq(j) <= b,
      All(j until i)(k => seq(k) <= b)
    )
    j = j-1
  }
  return true
}

@pure def sorted_lower_bound(seq: ISZ[Z], i: Z, b: Z): B = {
  Contract(
    Requires(sorted(seq), 0 <= i, i < seq.size, b < seq(i)),
    Ensures(Res == All(i until seq.size)(k => b < seq(k)) & Res == true)
  )
  var j: Z = i
  while (j < seq.size-1) {
    Invariant(
      Modifies(j),
      0 <= j,
      j < seq.size,
      b < seq(j),
      All(i until j)(k => b < seq(k))
    )
    j = j+1
  }
  return true
}

@pure def linsearch(seq: ISZ[Z], v: Z): Option[Z] = {
  Contract(
    Requires(sorted(seq)),
    Ensures(
      (Res == None[Z]()) | Exists(0 until seq.size)(i => seq(i) == v & Res == Some(i)))
  )
  var res: Option[Z] = None()
  var k: Z = 0
  while (k < seq.size) {
    Invariant(
      Modifies(res, k),
      k >= 0,
      k <= seq.size,
      (res == None[Z]()) | Exists(0 until k)(i => seq(i) == v & res == Some(i))
    )
    Deduce(|-((res == None[Z]()) | Exists(0 until k)(i => seq(i) == v & res == Some(i))))
    if (seq(k) == v) {
      res = Some(k)
      Deduce(|-(res == None[Z]() | Exists(0 until k + 1)(i => seq(i) == v & res == Some(i))))
    } else {
      Deduce(|-(res == None[Z]() | Exists(0 until k)(i => seq(i) == v & res == Some(i))))
    }
    Deduce(|-(res == None[Z]() | Exists(0 until k + 1)(i => seq(i) == v & res == Some(i))))
    k = k + 1
    Deduce(|-(res == None[Z]() | Exists(0 until k)(i => seq(i) == v & res == Some(i))))
  }
  return res
}

@pure def binsearch(seq: ISZ[Z], v: Z): Option[Z] = {
  Contract(
    Requires(sorted(seq)),
    Ensures(
      (Res == None[Z]()) | Exists(0 until seq.size)(i => seq(i) == v & Res == Some(i)))
  )
  if (seq.isEmpty) {
    return None()
  } else {
    Deduce(|-(seq.size > 0))
    if (seq.size == 1) {
      Deduce(|- (0 < seq.size))
      if (seq(0) == v) {
        return Some(0)
      } else {
        return None()
      }
    }
    var x: Z = 0
    var y: Z = seq.size - 1
    if (v < seq(x) | seq(y) < v) {
      return None()
    } else {
      if (seq(y) == v) {
        return Some(y)
      } else {
        while (x + 1 != y) {
          Invariant(
            Modifies(x, y),
            x >= 0,
            y < seq.size,
            x < y,
            seq(x) <= v,
            v < seq(y),
            All(0 until x)(i => seq(i) <= v),
            All(y until seq.size)(i => v < seq(i))
          )
          Deduce(|- (All(0 until x)(i => seq(i) <= v)))
          val h: Z = (x + y) / 2
          Deduce(|- (x <= h))
          Deduce(|- (h < y))
          if (seq(h) <= v) {
            Deduce(|- (sorted_upper_bound(seq, h, v)))
            Deduce(|- (All(0 until h)(i => seq(i) <= v)))
            x = h
          } else {
            Deduce(|- (sorted_lower_bound(seq, h, v)))
            Deduce(|- (All(y until seq.size)(i => v < seq(i))))
            y = h
          }
        }
        if (seq(x) == v) {
          return Some(x)
        } else {
          return None()
        }
      }
    }
  }
}

def merge(s: ISZ[Z], t: ISZ[Z]): ISZ[Z] = {

}