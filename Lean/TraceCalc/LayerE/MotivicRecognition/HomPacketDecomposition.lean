import TraceCalc.LayerE.MotivicRecognition.RecognitionTarget

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-- Minimal preadditive/enriched Hom API expected from the recognized category.
This is a theorem/construction input layer; it is not a proof that the ambient
recognized category already has these structures. -/
structure TraceMotivicPreadditiveHomData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  zeroHom :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      structuralRecognition.recognition.recognizedCategory.Hom X Y
  addHom :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      structuralRecognition.recognition.recognizedCategory.Hom X Y →
      structuralRecognition.recognition.recognizedCategory.Hom X Y →
      structuralRecognition.recognition.recognizedCategory.Hom X Y
  negHom :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      structuralRecognition.recognition.recognizedCategory.Hom X Y →
      structuralRecognition.recognition.recognizedCategory.Hom X Y
  comp_zero : Prop
  zero_comp : Prop
  comp_add : Prop
  add_comp : Prop

/-- Filtration data on recognized Hom spaces. This is the missing intermediate
layer between object packet cuts and associated packet/graded morphism pieces.
The current orthogonality theorem below does not yet consume the full filtered
API, but this structure records the semantically correct theorem frontier. -/
structure TraceMotivicHomFiltrationData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (preadditive : TraceMotivicPreadditiveHomData structuralRecognition) where
  homFiltration :
    (X Y : structuralRecognition.recognition.recognizedCategory.Object) →
      Int → structuralRecognition.recognition.recognizedCategory.Hom X Y → Prop
  zero_mem : Prop
  add_mem : Prop
  neg_mem : Prop
  comp_respects_filtration : Prop

/-- Packet-component shadow of recognized morphisms. This is not a claim that a
global morphism is a single packet morphism; it exposes the packet-indexed
component maps that a conservativity theorem can later inspect jointly. -/
structure TraceMotivicHomPacketComponentData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  PacketRecord :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  packetDegree :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      PacketRecord X → Int
  PacketHom :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      PacketRecord X → PacketRecord Y → Type z
  packetComponent :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      (sourcePacket : PacketRecord X) →
      (targetPacket : PacketRecord Y) →
      structuralRecognition.recognition.recognizedCategory.Hom X Y →
      PacketHom sourcePacket targetPacket
  packetZero :
    {X Y : structuralRecognition.recognition.recognizedCategory.Object} →
      {sourcePacket : PacketRecord X} → {targetPacket : PacketRecord Y} →
        PacketHom sourcePacket targetPacket → Prop

/-- Extensionality/conservativity input for packet components. If every relevant
packet component of a recognized morphism is zero, then the global morphism is
zero. This is the honest replacement for a literal packet lift. -/
structure TraceMotivicHomPacketExtensionality
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetData : TraceMotivicHomPacketComponentData structuralRecognition) where
  hom_zero_of_packet_family_vanishing :
    ∀ {X Y : structuralRecognition.recognition.recognizedCategory.Object}
      (f : structuralRecognition.recognition.recognizedCategory.Hom X Y)
      (sourceSupports : packetData.PacketRecord X → Prop)
      (targetSupports : packetData.PacketRecord Y → Prop)
      (sourceSupportWitness : {sourcePacket : packetData.PacketRecord X //
        sourceSupports sourcePacket})
      (targetSupportWitness : {targetPacket : packetData.PacketRecord Y //
        targetSupports targetPacket}),
        (∀ sourcePacket : packetData.PacketRecord X,
            ∀ targetPacket : packetData.PacketRecord Y,
              sourceSupports sourcePacket →
              targetSupports targetPacket →
              packetData.packetZero (packetData.packetComponent sourcePacket targetPacket f)) →
          TraceMotivicZeroMorphismWitness structuralRecognition f

/-- Separated-degree vanishing on packet components. This is the genuine lower
layer of orthogonality: incompatible source/target degrees force every packet
component to vanish. -/
structure TraceMotivicHomPacketSeparatedVanishing
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetData : TraceMotivicHomPacketComponentData structuralRecognition) where
  packet_vanishes_of_separated_degrees :
    ∀ {X Y : structuralRecognition.recognition.recognizedCategory.Object}
      (f : structuralRecognition.recognition.recognizedCategory.Hom X Y)
      (n : Int)
      (sourcePacket : packetData.PacketRecord X)
      (targetPacket : packetData.PacketRecord Y),
        packetData.packetDegree X sourcePacket ≤ n →
        n < packetData.packetDegree Y targetPacket →
        packetData.packetZero (packetData.packetComponent sourcePacket targetPacket f)

/-- Derived orthogonality theorem from Hom packet decomposition data.

The proof does not identify a global morphism with a single packet shadow.
Instead it shows that every supported packet component vanishes by separated
degrees, then invokes packet-component conservativity to conclude the global
morphism is zero. -/
def orthogonality_from_hom_packet_decomposition
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (packetData : TraceMotivicHomPacketComponentData structuralRecognition)
    (extensionality :
      TraceMotivicHomPacketExtensionality structuralRecognition packetData)
    (separatedVanishing :
      TraceMotivicHomPacketSeparatedVanishing structuralRecognition packetData)
    {n : Int}
    {X Y : structuralRecognition.recognition.recognizedCategory.Object}
    (f : structuralRecognition.recognition.recognizedCategory.Hom X Y)
    (sourceSupports : packetData.PacketRecord X → Prop)
    (targetSupports : packetData.PacketRecord Y → Prop)
    (sourceSupportWitness : {sourcePacket : packetData.PacketRecord X //
      sourceSupports sourcePacket})
    (targetSupportWitness : {targetPacket : packetData.PacketRecord Y //
      targetSupports targetPacket})
    (sourceDegreeBound :
      ∀ sourcePacket : packetData.PacketRecord X,
        sourceSupports sourcePacket → packetData.packetDegree X sourcePacket ≤ n)
    (targetDegreeBound :
      ∀ targetPacket : packetData.PacketRecord Y,
        targetSupports targetPacket → n + 1 ≤ packetData.packetDegree Y targetPacket) :
    TraceMotivicZeroMorphismWitness structuralRecognition f := by
  apply extensionality.hom_zero_of_packet_family_vanishing
    f sourceSupports targetSupports sourceSupportWitness targetSupportWitness
  intro sourcePacket targetPacket hSource hTarget
  apply separatedVanishing.packet_vanishes_of_separated_degrees f n sourcePacket targetPacket
  · exact sourceDegreeBound sourcePacket hSource
  ·
    have hStep : n < n + 1 := by
      simpa using Int.add_lt_add_left (show (0 : Int) < 1 by decide) n
    exact lt_of_lt_of_le hStep (targetDegreeBound targetPacket hTarget)

end MotivicRecognition
end TraceCalc