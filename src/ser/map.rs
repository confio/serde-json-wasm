use serde::ser;

use crate::ser::{Error, Result, Serializer};

pub struct SerializeMap<'a> {
    ser: &'a mut Serializer,
    first: bool,
}

impl<'a> SerializeMap<'a> {
    pub(crate) fn new(ser: &'a mut Serializer) -> Self {
        SerializeMap { ser, first: true }
    }
}

impl<'a> ser::SerializeMap for SerializeMap<'a> {
    type Ok = ();
    type Error = Error;

    fn end(self) -> Result<Self::Ok> {
        self.ser.push(b'}')?;
        Ok(())
    }

    fn serialize_key<T>(&mut self, key: &T) -> Result<()>
    where
        T: ser::Serialize + ?Sized,
    {
        if !self.first {
            self.ser.push(b',')?;
        }
        self.first = false;
        key.serialize(&mut *self.ser)?;
        self.ser.extend_from_slice(b":")?;
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<()>
    where
        T: ser::Serialize + ?Sized,
    {
        value.serialize(&mut *self.ser)?;
        Ok(())
    }
}
