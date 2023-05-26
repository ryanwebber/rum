use core::hash::Hash;
use std::collections::HashMap;

pub struct StringInterner<Symbol>
where
    Symbol: Eq + Hash + Clone + Ord + From<usize>,
{
    table: HashMap<String, Symbol>,
}

impl<Symbol> StringInterner<Symbol>
where
    Symbol: Eq + Hash + Clone + From<usize> + Ord,
{
    pub fn new() -> Self {
        StringInterner { table: HashMap::new() }
    }

    pub fn get<T>(&self, s: T) -> Option<Symbol>
    where
        T: AsRef<str>,
    {
        self.table.get(s.as_ref()).cloned()
    }

    pub fn get_or_intern<T>(&mut self, s: T) -> Symbol
    where
        T: AsRef<str>,
    {
        let s = s.as_ref();
        if let Some(sym) = self.get(s) {
            sym
        } else {
            let sym = Symbol::from(self.table.len());
            self.table.insert(s.into(), sym.clone());
            sym
        }
    }

    pub fn size(&self) -> usize {
        self.table.len()
    }

    pub fn resolve(&self, sym: Symbol) -> Option<&str> {
        self.table
            .iter()
            .find_map(|(k, v)| if v == &sym { Some(k.as_str()) } else { None })
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_insert() {
        let mut interner: StringInterner<usize> = StringInterner::new();
        let sym = interner.get_or_intern("hello");
        assert_eq!(interner.resolve(sym), Some("hello"));
        assert_eq!(interner.get("hello"), Some(sym));
    }

    #[test]
    fn test_equality() {
        let mut interner: StringInterner<usize> = StringInterner::new();
        let sym1 = interner.get_or_intern("hello");
        let sym2 = interner.get_or_intern("hello");
        assert_eq!(sym1, sym2);
        assert_eq!(interner.size(), 1);
    }
}
