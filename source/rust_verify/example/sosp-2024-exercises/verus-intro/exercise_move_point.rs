use vstd::prelude::*;
verus! {

#[derive(Debug, PartialEq)]
struct Point {
  x: i64,
}

impl Point {
  fn move_x(self, dx: i64) -> (r: Point)
    requires i64::MIN <= self.x + dx < i64::MAX,
    // ensures r.x == self.x + dx // <- change this
    ensures r == (Point { x: (self.x + dx) as i64 })
  {
    Point { x: self.x + dx }
  }

  spec fn center(self) -> bool {
    self.x == 0
  }
}

fn main() {
  let p1 = Point { x: 10 };
  let p2 = p1.move_x(-10);
  assert(p2.center());
}

} // verus!
