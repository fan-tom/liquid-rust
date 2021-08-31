use rustproof_libsmt::backends::{z3::Z3 as Imp, smtlib2::SMTProc};
use std::{
    io::{
        Read,
        BufReader,
        self
    },
    fs::File,
    env::VarError,
};
use std::ops::{Deref, DerefMut};
use std::path::Path;
use std::io::ErrorKind;

pub struct Z3 {
    inner: Imp
}

pub struct Scope<'a> {
    z3: &'a mut Z3
}

impl Deref for Scope<'_ > {
    type Target = Imp;

    fn deref(&self) -> &Self::Target {
        &self.z3
    }
}

impl DerefMut for Scope<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.z3
    }
}

impl Drop for Scope<'_> {
    fn drop(&mut self) {
        self.z3.pop();
    }
}

impl Z3 {
    pub fn feed_file(&mut self, path: impl AsRef<Path>) -> Result<(), io::Error> {
        let mut file = BufReader::new(File::open(path)?);
        // TODO: pipe without reading too much into memory, quick'n'dirty impl
        let mut content = String::new();
        file.read_to_string(&mut content)?;
        self.inner.write(content).map_err(|_| ErrorKind::Other.into())
    }

    pub fn feed_string(&mut self, content: &str) -> Result<(), String> {
        self.inner.write(content)
    }

    fn push(&mut self) -> Result<(), String> {
        self.inner.write("(push)\n")
    }

    fn pop(&mut self) -> Result<(), String> {
        self.inner.write("(pop)\n")
    }

    pub fn scope(&mut self) -> Scope {
        self.push().expect("Cannot create scope");
        Scope { z3: self }
    }
}

impl Deref for Z3 {
    type Target = Imp;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for Z3 {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl Default for Z3 {
    fn default() -> Self {
        let z3 = match std::env::var("LIQUID_Z3") {
            Ok(z3exec) => Imp::new_with_binary(&z3exec),
            Err(VarError::NotPresent) => {
                let mut res = Imp::default();
                res.init();
                res
            }
            Err(VarError::NotUnicode(path)) => panic!("Non-unicode path to Z3 executable: {:?}", path)
        };
        Self {
            inner: z3
        }
    }
}