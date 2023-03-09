// #Sireum #Logika
import org.sireum._

var z: Z = 0

def max(x: Z, y: Z) {
  Contract(
    Requires(x > 0, y > 0),
    Modifies(z),
    Ensures(z == x | z == y, x <= z, y <= z)
  )
  if (x < y) {
    z = y
  } else {
    z = x
  }
}

// x > 0 & y > 0 & x < y & z == y & (z == x | z == y) & x <= z & y <= z
// satisfied by
//   input: x == 1 & y == 2
//   output: z == 2
// because
//   1 > 0 & 2 > 0 & 1 < 2 & 2 == 2 & (2 == 1 | 2 == 2) & 1 <= 2 & 2 <= 2
// ---
// x > 0 & y > 0 & x >= y & z == x & (z == x | z == y) & x <= z & y <= z
// satisfied by (x == y)
//   input: x == 1 & y == 1
//   output: z == 1
// because
//   1 > 0 & 1 > 0 & 1 >= 1 & 1 == 1 & (1 == 1 | 1 == 1) & 1 <= 1 & 1 <= 1
// ---
// x > 0 & y > 0 & x >= y & z == x & (z == x | z == y) & x <= z & y <= z
// satisfied by (x > y)
//   input: x == 2 & y == 1
//   output: z == 2
// because
//   2 > 0 & 1 > 0 & 2 >= 1 & 2 == 2 & (2 == 2 | 2 == 1) & 2 <= 2 & 1 <= 2