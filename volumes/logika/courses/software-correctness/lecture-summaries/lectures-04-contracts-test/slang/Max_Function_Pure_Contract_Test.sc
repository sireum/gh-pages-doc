// #Sireum #Logika
import org.sireum._

def max(x: Z, y: Z): Z = {
  Contract(
    Requires(x > 0, y > 0),
    Ensures(Res == x | Res == y, x <= Res, y <= Res)
  )
  if (x < y) {
    return y // "Res = y"
  } else {
    return x // "Res = x"
  }
}

// x > 0 & y > 0 & x < y & Res == y & (Res == x | Res == y) & x <= Res & y <= Res
// satisfied by
//   input: x == 1 & y == 2
//   output: Res == 2
// because
//   1 > 0 & 2 > 0 & 1 < 2 & 2 == 2 & (2 == 1 | 2 == 2) & 1 <= 2 & 2 <= 2
// ---
// x > 0 & y > 0 & x >= y & Res == x & (Res == x | Res == y) & x <= Res & y <= Res
// satisfied by (x == y)
//   input: x == 1 & y == 1
//   output: Res == 1
// because
//   1 > 0 & 1 > 0 & 1 >= 1 & 1 == 1 & (1 == 1 | 1 == 1) & 1 <= 1 & 1 <= 1
// ---
// x > 0 & y > 0 & x >= y & Res == x & (Res == x | Res == y) & x <= Res & y <= Res
// satisfied by (x > y)
//   input: x == 2 & y == 1
//   output: Res == 2
// because
//   2 > 0 & 1 > 0 & 2 >= 1 & 2 == 2 & (2 == 2 | 2 == 1) & 2 <= 2 & 1 <= 2