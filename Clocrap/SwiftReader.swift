// Reads Swift files with SwiftSyntax, the parser the compiler itself uses, and prints each file's
// functions. `Clocrap/SwiftReader.lean` builds this on first use and runs it.
//
// Input, on standard input: paths, each followed by a NUL.
// Output: one line per function, in source order within each file, with tabs between
// the path's index, its first line, its last line, its complexity and its name.
//
// Both branches of a `#if` are read, as neither can be ruled out without the build's flags.

import Foundation
import SwiftParser
import SwiftSyntax

struct Found {
  var name: String
  var first: Int
  var last: Int
  var complexity = 1
}

final class Reader: SyntaxVisitor {
  private let lines: SourceLocationConverter
  private var found: [Found] = []
  /// The functions being read, outermost first, as indices into `found`.
  private var open: [Int] = []

  init(_ lines: SourceLocationConverter) {
    self.lines = lines
    super.init(viewMode: .sourceAccurate)
  }

  static func functions(in tree: SourceFileSyntax, _ lines: SourceLocationConverter) -> [Found] {
    let reader = Reader(lines)
    reader.walk(tree)
    return reader.found
  }

  private func line(_ position: AbsolutePosition) -> Int {
    lines.location(for: position).line
  }

  private func enter(_ name: String, from first: some SyntaxProtocol, to last: some SyntaxProtocol) {
    open.append(found.count)
    found.append(Found(
      name: name,
      first: line(first.positionAfterSkippingLeadingTrivia),
      last: line(last.endPositionBeforeTrailingTrivia)))
  }

  private func decide(_ by: Int = 1) -> SyntaxVisitorContinueKind {
    if let current = open.last { found[current].complexity += by }
    return .visitChildren
  }

  // Declarations. One with no body, as in a protocol, has nothing to run.

  override func visit(_ node: FunctionDeclSyntax) -> SyntaxVisitorContinueKind {
    if node.body != nil { enter(node.name.text, from: node, to: node) }
    return .visitChildren
  }

  override func visitPost(_ node: FunctionDeclSyntax) {
    if node.body != nil { open.removeLast() }
  }

  override func visit(_ node: InitializerDeclSyntax) -> SyntaxVisitorContinueKind {
    if node.body != nil { enter("init", from: node, to: node) }
    return .visitChildren
  }

  override func visitPost(_ node: InitializerDeclSyntax) {
    if node.body != nil { open.removeLast() }
  }

  override func visit(_ node: DeinitializerDeclSyntax) -> SyntaxVisitorContinueKind {
    if node.body != nil { enter("deinit", from: node, to: node) }
    return .visitChildren
  }

  override func visitPost(_ node: DeinitializerDeclSyntax) {
    if node.body != nil { open.removeLast() }
  }

  /// The property or subscript a block of accessors belongs to: its name, and where it starts.
  private func owner(of block: AccessorBlockSyntax) -> (name: String, first: Syntax) {
    if let binding = block.parent?.as(PatternBindingSyntax.self) {
      let declaration = binding.parent?.parent ?? Syntax(binding)
      return (binding.pattern.trimmedDescription, declaration)
    }
    return ("subscript", block.parent ?? Syntax(block))
  }

  private func isGetterShorthand(_ node: AccessorBlockSyntax) -> Bool {
    if case .getter = node.accessors { return true }
    return false
  }

  /// `var x: Int { … }` and `subscript(i: Int) -> Int { … }`, which are getters with no `get`.
  override func visit(_ node: AccessorBlockSyntax) -> SyntaxVisitorContinueKind {
    if isGetterShorthand(node) {
      let (name, first) = owner(of: node)
      enter(name, from: first, to: node)
    }
    return .visitChildren
  }

  override func visitPost(_ node: AccessorBlockSyntax) {
    if isGetterShorthand(node) { open.removeLast() }
  }

  override func visit(_ node: AccessorDeclSyntax) -> SyntaxVisitorContinueKind {
    if node.body != nil, let block = node.parent?.parent?.as(AccessorBlockSyntax.self) {
      enter("\(owner(of: block).name).\(node.accessorSpecifier.text)", from: node, to: node)
    }
    return .visitChildren
  }

  override func visitPost(_ node: AccessorDeclSyntax) {
    if node.body != nil, node.parent?.parent?.is(AccessorBlockSyntax.self) == true {
      open.removeLast()
    }
  }

  // Decisions.

  override func visit(_ node: IfExprSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: GuardStmtSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: ForStmtSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: WhileStmtSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: RepeatStmtSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: CatchClauseSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: SwitchCaseSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: SwitchExprSyntax) -> SyntaxVisitorContinueKind { decide(-1) }
  override func visit(_ node: UnresolvedTernaryExprSyntax) -> SyntaxVisitorContinueKind { decide() }
  override func visit(_ node: TernaryExprSyntax) -> SyntaxVisitorContinueKind { decide() }

  override func visit(_ node: BinaryOperatorExprSyntax) -> SyntaxVisitorContinueKind {
    switch node.operator.text {
    case "&&", "||", "??": return decide()
    default: return .visitChildren
    }
  }

  /// A `#if` line's condition is not code: only the clause's body is read.
  override func visit(_ node: IfConfigClauseSyntax) -> SyntaxVisitorContinueKind {
    if let elements = node.elements { walk(elements) }
    return .skipChildren
  }
}

func read(_ path: String) -> [Found]? {
  guard let source = FileManager.default.contents(atPath: path) else { return nil }
  let tree = source.withUnsafeBytes { bytes in
    Parser.parse(source: bytes.bindMemory(to: UInt8.self))
  }
  return Reader.functions(in: tree, SourceLocationConverter(fileName: path, tree: tree))
}

let input = FileHandle.standardInput.readDataToEndOfFile()
let paths = input.split(separator: 0).map { String(decoding: $0, as: UTF8.self) }
var results = [[Found]?](repeating: nil, count: paths.count)
results.withUnsafeMutableBufferPointer { slots in
  // Each thread writes its own slot.
  nonisolated(unsafe) let slots = slots
  DispatchQueue.concurrentPerform(iterations: paths.count) { index in
    slots[index] = read(paths[index])
  }
}

var output = ""
for (index, functions) in results.enumerated() {
  guard let functions else {
    FileHandle.standardError.write(Data("clocrap: \(paths[index]): could not read\n".utf8))
    continue
  }
  for f in functions {
    output += "\(index)\t\(f.first)\t\(f.last)\t\(f.complexity)\t\(f.name)\n"
  }
}
FileHandle.standardOutput.write(Data(output.utf8))
