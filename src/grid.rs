use std::ops::Range;

pub fn grid(
    v: (usize, usize),
    d: &[(isize, isize)],
    h: Range<usize>,
    w: Range<usize>,
) -> impl Iterator<Item = (usize, usize)> + '_ {
    let v = (v.0 as isize, v.1 as isize);
    let w = w.start as isize..w.end as isize;
    let h = h.start as isize..h.end as isize;
    d.iter().filter_map(move |(dy, dx)| {
        let (ny, nx) = (dy + v.0, dx + v.1);
        if h.contains(&ny) && w.contains(&nx) {
            Some((ny as usize, nx as usize))
        } else {
            None
        }
    })
}

pub fn grid_4(
    v: (usize, usize),
    h: Range<usize>,
    w: Range<usize>,
) -> impl Iterator<Item = (usize, usize)> {
    grid(v, &[(1, 0), (0, 1), (-1, 0), (0, -1)], h, w)
}

pub fn grid_8(
    v: (usize, usize),
    h: Range<usize>,
    w: Range<usize>,
) -> impl Iterator<Item = (usize, usize)> {
    grid(
        v,
        &[
            (1, 0),
            (1, 1),
            (0, 1),
            (-1, 1),
            (-1, 0),
            (-1, -1),
            (0, -1),
            (1, -1),
        ],
        h,
        w,
    )
}

#[test]
fn test_grid() {
    use itertools::*;
    assert_equal(
        grid_4((1, 1), 0..3, 0..3),
        vec![(2, 1), (1, 2), (0, 1), (1, 0)],
    );
    assert_equal(grid_4((0, 1), 0..3, 0..3), vec![(1, 1), (0, 2), (0, 0)]);
}
