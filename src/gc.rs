use core::{fmt, hash::Hash};
use std::{
    cell::{BorrowError, BorrowMutError, Ref, RefCell, RefMut},
    cmp::PartialEq,
    fmt::Debug,
    fmt::{Display, Formatter},
    ops::Deref,
    rc::Rc,
};

pub struct Gc<T>(Rc<RefCell<T>>);

impl<T> PartialEq for Gc<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref().borrow().eq(&*other.0.as_ref().borrow())
    }
}

impl<T> Eq for Gc<T> where T: Eq {}

impl<T> Hash for Gc<T>
where
    T: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_ref().borrow().hash(state)
    }
}

impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        Gc(self.0.clone())
    }
}

impl<T> Debug for Gc<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.as_ref().borrow().fmt(f)
    }
}

impl<T> Display for Gc<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.as_ref().borrow().fmt(f)
    }
}

impl<T> Deref for Gc<T> {
    type Target = RefCell<T>;
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

#[allow(dead_code)]
impl<T> Gc<T> {
    pub fn new(value: T) -> Self {
        Self(Rc::new(RefCell::new(value)))
    }

    pub fn try_unwrap(self) -> Result<T, Self> {
        Rc::try_unwrap(self.0).map(RefCell::into_inner).map_err(Self)
    }

    pub fn unwrap(self) -> T {
        self.try_unwrap().ok().unwrap()
    }

    pub fn weak_count(this: &Self) -> usize {
        Rc::weak_count(&this.0)
    }

    pub fn strong_count(this: &Self) -> usize {
        Rc::strong_count(&this.0)
    }

    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        Rc::ptr_eq(&this.0, &other.0)
    }

    pub fn try_borrow(&self) -> Result<Ref<T>, BorrowError> {
        self.0.try_borrow()
    }

    pub fn try_borrow_mut(&self) -> Result<RefMut<T>, BorrowMutError> {
        self.0.try_borrow_mut()
    }

    pub fn borrow(&self) -> Ref<T> {
        self.0.as_ref().borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<T> {
        self.0.borrow_mut()
    }
}
