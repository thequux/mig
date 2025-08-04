// SPDX-License-Identifier: MIT
use anyhow::anyhow;
use std::borrow::Cow;
use std::path::Path;

pub type SourceItem<'a> = anyhow::Result<(Cow<'a, str>, Cow<'a, [u8]>)>;

pub struct DirSource {
    dir: std::fs::ReadDir,
}

impl DirSource {
    pub fn new(dir: impl AsRef<Path>) -> Result<Self, std::io::Error> {
        Ok(Self {
            dir: dir.as_ref().read_dir()?,
        })
    }
}

impl Iterator for DirSource {
    type Item = SourceItem<'static>;
    fn next(&mut self) -> Option<Self::Item> {
        let dirent = self.dir.next()?;

        Some((move || {
            let dirent = dirent?;
            let path = dirent.path();
            let name = dirent
                .file_name()
                .to_str()
                .ok_or_else(|| {
                    anyhow::format_err!("Invalid unicode in filename: {:?}", path.file_name())
                })?
                .to_owned();

            let content = std::fs::read(path)?;

            Ok((name.to_owned().into(), content.into()))
        })())
    }
}

// rust-embed 8
#[cfg(feature = "rust-embed_8")]
pub struct RustEmbedSource<T: rust_embed::RustEmbed> {
    names: rust_embed::Filenames,
    phantom: std::marker::PhantomData<T>,
}

#[cfg(feature = "rust-embed_8")]
impl<T: rust_embed::RustEmbed> Default for RustEmbedSource<T> {
    fn default() -> Self {
        Self {
            names: T::iter(),
            phantom: std::marker::PhantomData,
        }
    }
}

#[cfg(feature = "rust-embed_8")]
impl<T: rust_embed::RustEmbed> Iterator for RustEmbedSource<T> {
    type Item = SourceItem<'static>;
    fn next(&mut self) -> Option<Self::Item> {
        let name = self.names.next()?;
        let content = T::get(&name)?.data;
        Some(Ok((name.into(), content)))
    }
}

// include_dir 0.7
#[cfg(feature = "include_dir_07")]
pub struct IncludeDirSource<'a> {
    contents: std::vec::IntoIter<&'a include_dir::File<'a>>,
}

#[cfg(feature = "include_dir_07")]
impl<'a> IncludeDirSource<'a> {
    pub fn new(dir: &'a include_dir::Dir<'a>) -> Self {
        Self {
            contents: dir.files().collect::<Vec<_>>().into_iter(),
        }
    }
}

#[cfg(feature = "include_dir_07")]
impl<'a> Iterator for IncludeDirSource<'a> {
    type Item = SourceItem<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let file = self.contents.next()?;

        let path = file.path();
        Some((|| {
            let name = path.file_name().unwrap().to_str().ok_or_else(|| {
                anyhow!(
                    "Invalid unicode in filename {:?}",
                    path.file_name().unwrap(),
                )
            })?;
            let content = file.contents();

            Ok((name.into(), content.into()))
        })())
    }
}
