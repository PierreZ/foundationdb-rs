(function() {var type_impls = {
"foundationdb_simulation":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Clone-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/1.79.0/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/clone.rs.html#169\">source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;Self</a>)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/1.79.0/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Debug-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/1.79.0/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/1.79.0/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Default-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Default-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.default\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.default\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/default/trait.Default.html#tymethod.default\" class=\"fn\">default</a>() -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;</h4></section></summary><div class='docblock'>Returns the “default value” for a type. <a href=\"https://doc.rust-lang.org/1.79.0/core/default/trait.Default.html#tymethod.default\">Read more</a></div></details></div></details>","Default","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Deref-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#149\">source</a></span><a href=\"#impl-Deref-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/ops/deref/trait.Deref.html\" title=\"trait core::ops::deref::Deref\">Deref</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle\" open><summary><section id=\"associatedtype.Target\" class=\"associatedtype trait-impl\"><a href=\"#associatedtype.Target\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"https://doc.rust-lang.org/1.79.0/core/ops/deref/trait.Deref.html#associatedtype.Target\" class=\"associatedtype\">Target</a> = T</h4></section></summary><div class='docblock'>The resulting type after dereferencing.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.deref\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#152\">source</a><a href=\"#method.deref\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/ops/deref/trait.Deref.html#tymethod.deref\" class=\"fn\">deref</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;T</a></h4></section></summary><div class='docblock'>Dereferences the value.</div></details></div></details>","Deref","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-DerefMut-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#158\">source</a></span><a href=\"#impl-DerefMut-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/ops/deref/trait.DerefMut.html\" title=\"trait core::ops::deref::DerefMut\">DerefMut</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.deref_mut\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#160\">source</a><a href=\"#method.deref_mut\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/ops/deref/trait.DerefMut.html#tymethod.deref_mut\" class=\"fn\">deref_mut</a>(&amp;mut self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;mut T</a></h4></section></summary><div class='docblock'>Mutably dereferences the value.</div></details></div></details>","DerefMut","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Hash-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Hash-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.hash\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/hash/trait.Hash.html#tymethod.hash\" class=\"fn\">hash</a>&lt;__H&gt;(&amp;self, state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;mut __H</a>)<div class=\"where\">where\n    __H: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,</div></h4></section></summary><div class='docblock'>Feeds this value into the given <a href=\"https://doc.rust-lang.org/1.79.0/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/1.79.0/core/hash/trait.Hash.html#tymethod.hash\">Read more</a></div></details></div></details>","Hash","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ManuallyDrop%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#117\">source</a><a href=\"#impl-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.drop\" class=\"method\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#140\">source</a></span><h4 class=\"code-header\">pub unsafe fn <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#tymethod.drop\" class=\"fn\">drop</a>(slot: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;)</h4></section></summary><div class=\"docblock\"><p>Manually drops the contained value. This is exactly equivalent to calling\n<a href=\"https://doc.rust-lang.org/1.79.0/core/ptr/fn.drop_in_place.html\" title=\"fn core::ptr::drop_in_place\"><code>ptr::drop_in_place</code></a> with a pointer to the contained value. As such, unless\nthe contained value is a packed struct, the destructor will be called in-place\nwithout moving the value, and thus can be used to safely drop <a href=\"https://doc.rust-lang.org/1.79.0/core/pin/index.html\" title=\"mod core::pin\">pinned</a> data.</p>\n<p>If you have ownership of the value, you can use <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#method.into_inner\" title=\"associated function core::mem::manually_drop::ManuallyDrop::into_inner\"><code>ManuallyDrop::into_inner</code></a> instead.</p>\n<h5 id=\"safety\"><a class=\"doc-anchor\" href=\"#safety\">§</a>Safety</h5>\n<p>This function runs the destructor of the contained value. Other than changes made by\nthe destructor itself, the memory is left unchanged, and so as far as the compiler is\nconcerned still holds a bit-pattern which is valid for the type <code>T</code>.</p>\n<p>However, this “zombie” value should not be exposed to safe code, and this function\nshould not be called more than once. To use a value after it’s been dropped, or drop\na value multiple times, can cause Undefined Behavior (depending on what <code>drop</code> does).\nThis is normally prevented by the type system, but users of <code>ManuallyDrop</code> must\nuphold those guarantees without assistance from the compiler.</p>\n</div></details></div></details>",0,"foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ManuallyDrop%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#54\">source</a><a href=\"#impl-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.new\" class=\"method\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0, const since 1.32.0\">1.20.0 (const: 1.32.0)</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#70\">source</a></span><h4 class=\"code-header\">pub const fn <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#tymethod.new\" class=\"fn\">new</a>(value: T) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;</h4></section></summary><div class=\"docblock\"><p>Wrap a value to be manually dropped.</p>\n<h5 id=\"examples\"><a class=\"doc-anchor\" href=\"#examples\">§</a>Examples</h5>\n<div class=\"example-wrap\"><pre class=\"rust rust-example-rendered\"><code><span class=\"kw\">use </span>std::mem::ManuallyDrop;\n<span class=\"kw\">let </span><span class=\"kw-2\">mut </span>x = ManuallyDrop::new(String::from(<span class=\"string\">\"Hello World!\"</span>));\nx.truncate(<span class=\"number\">5</span>); <span class=\"comment\">// You can still safely operate on the value\n</span><span class=\"macro\">assert_eq!</span>(<span class=\"kw-2\">*</span>x, <span class=\"string\">\"Hello\"</span>);\n<span class=\"comment\">// But `Drop` will not be run here</span></code></pre></div>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.into_inner\" class=\"method\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0, const since 1.32.0\">1.20.0 (const: 1.32.0)</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#88\">source</a></span><h4 class=\"code-header\">pub const fn <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#tymethod.into_inner\" class=\"fn\">into_inner</a>(slot: <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;) -&gt; T</h4></section></summary><div class=\"docblock\"><p>Extracts the value from the <code>ManuallyDrop</code> container.</p>\n<p>This allows the value to be dropped again.</p>\n<h5 id=\"examples-1\"><a class=\"doc-anchor\" href=\"#examples-1\">§</a>Examples</h5>\n<div class=\"example-wrap\"><pre class=\"rust rust-example-rendered\"><code><span class=\"kw\">use </span>std::mem::ManuallyDrop;\n<span class=\"kw\">let </span>x = ManuallyDrop::new(Box::new(()));\n<span class=\"kw\">let _</span>: Box&lt;()&gt; = ManuallyDrop::into_inner(x); <span class=\"comment\">// This drops the `Box`.</span></code></pre></div>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.take\" class=\"method\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.42.0\">1.42.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#110\">source</a></span><h4 class=\"code-header\">pub unsafe fn <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#tymethod.take\" class=\"fn\">take</a>(slot: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;) -&gt; T</h4></section></summary><div class=\"docblock\"><p>Takes the value from the <code>ManuallyDrop&lt;T&gt;</code> container out.</p>\n<p>This method is primarily intended for moving out values in drop.\nInstead of using <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#method.drop\" title=\"associated function core::mem::manually_drop::ManuallyDrop::drop\"><code>ManuallyDrop::drop</code></a> to manually drop the value,\nyou can use this method to take the value and use it however desired.</p>\n<p>Whenever possible, it is preferable to use <a href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html#method.into_inner\" title=\"associated function core::mem::manually_drop::ManuallyDrop::into_inner\"><code>into_inner</code></a>\ninstead, which prevents duplicating the content of the <code>ManuallyDrop&lt;T&gt;</code>.</p>\n<h5 id=\"safety\"><a class=\"doc-anchor\" href=\"#safety\">§</a>Safety</h5>\n<p>This function semantically moves out the contained value without preventing further usage,\nleaving the state of this container unchanged.\nIt is your responsibility to ensure that this <code>ManuallyDrop</code> is not used again.</p>\n</div></details></div></details>",0,"foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Ord-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Ord-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.cmp\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.cmp\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.Ord.html#tymethod.cmp\" class=\"fn\">cmp</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/enum.Ordering.html\" title=\"enum core::cmp::Ordering\">Ordering</a></h4></section></summary><div class='docblock'>This method returns an <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/enum.Ordering.html\" title=\"enum core::cmp::Ordering\"><code>Ordering</code></a> between <code>self</code> and <code>other</code>. <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.Ord.html#tymethod.cmp\">Read more</a></div></details></div></details>","Ord","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-PartialEq-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests for <code>self</code> and <code>other</code> values to be equal, and is used\nby <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/cmp.rs.html#263\">source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests for <code>!=</code>. The default implementation is almost always\nsufficient, and should not be overridden without very good reason.</div></details></div></details>","PartialEq","foundationdb_simulation::SimDatabase"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialOrd-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-PartialOrd-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html\" title=\"trait core::cmp::PartialOrd\">PartialOrd</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html\" title=\"trait core::cmp::PartialOrd\">PartialOrd</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.partial_cmp\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a><a href=\"#method.partial_cmp\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#tymethod.partial_cmp\" class=\"fn\">partial_cmp</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/1.79.0/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;<a class=\"enum\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/enum.Ordering.html\" title=\"enum core::cmp::Ordering\">Ordering</a>&gt;</h4></section></summary><div class='docblock'>This method returns an ordering between <code>self</code> and <code>other</code> values if one exists. <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#tymethod.partial_cmp\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.lt\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/cmp.rs.html#1179\">source</a></span><a href=\"#method.lt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.lt\" class=\"fn\">lt</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests less than (for <code>self</code> and <code>other</code>) and is used by the <code>&lt;</code> operator. <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.lt\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.le\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/cmp.rs.html#1197\">source</a></span><a href=\"#method.le\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.le\" class=\"fn\">le</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests less than or equal to (for <code>self</code> and <code>other</code>) and is used by the <code>&lt;=</code>\noperator. <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.le\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.gt\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/cmp.rs.html#1214\">source</a></span><a href=\"#method.gt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.gt\" class=\"fn\">gt</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests greater than (for <code>self</code> and <code>other</code>) and is used by the <code>&gt;</code> operator. <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.gt\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ge\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/cmp.rs.html#1232\">source</a></span><a href=\"#method.ge\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.ge\" class=\"fn\">ge</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/1.79.0/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests greater than or equal to (for <code>self</code> and <code>other</code>) and is used by the <code>&gt;=</code>\noperator. <a href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.PartialOrd.html#method.ge\">Read more</a></div></details></div></details>","PartialOrd","foundationdb_simulation::SimDatabase"],["<section id=\"impl-Copy-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Copy-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Copy.html\" title=\"trait core::marker::Copy\">Copy</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section>","Copy","foundationdb_simulation::SimDatabase"],["<section id=\"impl-Eq-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-Eq-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section>","Eq","foundationdb_simulation::SimDatabase"],["<section id=\"impl-StructuralPartialEq-for-ManuallyDrop%3CT%3E\" class=\"impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.20.0\">1.20.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/1.79.0/src/core/mem/manually_drop.rs.html#48\">source</a></span><a href=\"#impl-StructuralPartialEq-for-ManuallyDrop%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.StructuralPartialEq.html\" title=\"trait core::marker::StructuralPartialEq\">StructuralPartialEq</a> for <a class=\"struct\" href=\"https://doc.rust-lang.org/1.79.0/core/mem/manually_drop/struct.ManuallyDrop.html\" title=\"struct core::mem::manually_drop::ManuallyDrop\">ManuallyDrop</a>&lt;T&gt;<div class=\"where\">where\n    T: ?<a class=\"trait\" href=\"https://doc.rust-lang.org/1.79.0/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h3></section>","StructuralPartialEq","foundationdb_simulation::SimDatabase"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()