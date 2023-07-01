use crate::object::Object;

pub const FIELD_COUNT: usize = 3;

pub struct Rib<'a> {
    fields: &'a [Object; FIELD_COUNT],
}

impl<'a> Rib<'a> {
    pub fn new(fields: &'a [Object; FIELD_COUNT]) -> Self {
        Self { fields }
    }

    pub fn car(&self) -> Object {
        self.fields[0]
    }

    pub fn cdr(&self) -> Object {
        self.fields[1]
    }

    pub fn tag(&self) -> Object {
        self.fields[2]
    }
}
