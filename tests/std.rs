extern crate result_float;

use result_float::rf;

#[test]
fn test_display() {
    assert_eq!(format!("{}", rf(3.14).unwrap()), "3.14");
}
