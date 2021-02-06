#[test]
fn test_equip_remove_tests() {
    use std::process::{Command, Stdio};
    if !Command::new("cargo")
        .arg("equip")
        .arg("-V")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .expect("failed to execute process")
        .success()
    {
        // system didn't install cargo-equip
        return;
    }

    // cargo equip --resolve-cfgs --remove docs comments --rustfmt --exclude-atcoder-crates --check
    let e = std::process::Command::new("cargo")
        .arg("equip")
        .arg("--resolve-cfgs")
        .arg("--remove")
        .arg("docs")
        .arg("comments")
        .arg("--rustfmt")
        .arg("--exclude-atcoder-crates")
        .arg("--check")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("failed to execute process");

    assert_eq!(e.status.success(), true);
    use itertools::Itertools;
    let s = std::str::from_utf8(&e.stdout).expect("failed to execute process");
    for (i, (l1, l2)) in s.lines().tuple_windows().enumerate() {
        if l1.find("#[test]") != None {
            let msg = format!(
                "find `#[test]` \n >>> {}:  {}\n >>> {}:  {}",
                i + 1,
                l1,
                i + 2,
                l2
            );
            Option::<()>::None.expect(&msg);
        }
    }
}
