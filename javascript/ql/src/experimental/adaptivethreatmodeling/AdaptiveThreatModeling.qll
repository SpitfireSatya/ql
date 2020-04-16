external private predicate adaptiveThreatModelingModels(
  string modelChecksum, string modelLanguage, string modelName, string modelType
);

private import javascript as raw
private import raw::DataFlow as DataFlow
import ATMConfig

module ATMEmbeddings {
  private import CodeToFeatures::DatabaseFeatures as DatabaseFeatures

  class Entity = DatabaseFeatures::Entity;

  /* Currently the only label is a label marking an embedding as derived from an entity in the current database. */
  private newtype TEmbeddingLabel = TEntityLabel(Entity entity)

  /**
   * An abstract label that can be used to mark an embedding with the object from which it has been
   * derived.
   */
  abstract class EmbeddingLabel extends TEmbeddingLabel {
    abstract string toString();
  }

  /** A label marking an embedding as derived from an entity in the current snapshot. */
  class EntityLabel extends EmbeddingLabel {
    private Entity entity;

    EntityLabel() { this = TEntityLabel(entity) }

    Entity getEntity() { result = entity }

    override string toString() { result = "EntityLabel(" + entity.toString() + ")" }
  }

  /**
   * `entities` relation suitable for passing to the `codeEmbedding` HOP.
   *
   * The `codeEmbedding` HOP expects an entities relation with eight columns, while
   * `DatabaseFeatures` generates one with nine columns.
   */
  predicate entities(
    Entity entity, string entityName, string entityType, string path, int startLine,
    int startColumn, int endLine, int endColumn
  ) {
    DatabaseFeatures::entities(entity, entityName, entityType, path, startLine, startColumn,
      endLine, endColumn, _)
  }

  private predicate snapshotEmbeddingsByEntity(
    Entity entity, int embeddingIndex, float embeddingValue
  ) =
    codeEmbedding(entities/8, DatabaseFeatures::astNodes/5, DatabaseFeatures::nodeAttributes/2,
      modelChecksum/0)(entity, embeddingIndex, embeddingValue)

  /** Embeddings for each entity in the current snapshot. */
  predicate snapshotEmbeddings(EntityLabel label, int embeddingIndex, float embeddingValue) {
    exists(Entity entity |
      snapshotEmbeddingsByEntity(entity, embeddingIndex, embeddingValue) and
      label.getEntity() = entity
    )
  }

  /** Checksum of the model that should be used. */
  string modelChecksum() { adaptiveThreatModelingModels(result, "javascript", _, _) }
}

private module ATMEmbeddingsDebugging {
  query predicate snapshotEmbeddingsDebug = ATMEmbeddings::snapshotEmbeddings/3;

  query predicate modelChecksumDebug = ATMEmbeddings::modelChecksum/0;
}

private ATMConfig getCfg() { any() }

module Mappers {
  private import CodeToFeatures

  /**
   * This modules provides logic to map a sink to a `raw::Function`.
   */
  private module SinkToFunctionNoSQL {
    private raw::Function getNamedEnclosingFunction(raw::Function f) {
      if not exists(f.getName())
      then result = getNamedEnclosingFunction(f.getEnclosingContainer())
      else result = f
    }

    private raw::Function nodeToNamedFunction(DataFlow::Node node) {
      result = getNamedEnclosingFunction(node.getContainer())
    }

    /**
     * We use the innermost named function that encloses a sink, if one exists.
     * Otherwise, we use the innermost function that encloses the sink.
     */
    raw::Function sinkToFunction(DataFlow::Node sink) {
      if exists(raw::Function f | f = nodeToNamedFunction(sink))
      then result = nodeToNamedFunction(sink)
      else result = sink.getContainer()
    }
  }

  private DatabaseFeatures::Entity getFirstExtractedEntity(raw::Function e) {
    if
      DatabaseFeatures::entities(result, _, _, _, _, _, _, _, _) and
      result.getDefinedFunction() = e
    then any()
    else result = getFirstExtractedEntity(e.getEnclosingContainer())
  }

  /** Map from a sink to an entity */
  DatabaseFeatures::Entity getEntityFromSink(DataFlow::Node sink) {
    result = getFirstExtractedEntity(SinkToFunctionNoSQL::sinkToFunction(sink))
  }

  /** Map from an entity to a sink */
  DataFlow::Node getSinkCandidateWithinEntity(DatabaseFeatures::Entity entity) {
    getCfg().isEffectiveSink(result) and
    result.getContainer().getEnclosingContainer*() = entity.getDefinedFunction()
  }
}

// To debug the Mappers module, import this module by adding "import MappersDebugging" to the top-level.
module MappersDebugging {
  private import CodeToFeatures

  query predicate snapshotSinks(DataFlow::Node sink) {
    exists(DatabaseFeatures::Entity entity |
      DatabaseFeatures::entities(entity, _, _, _, _, _, _, _, _) and
      sink = Mappers::getSinkCandidateWithinEntity(entity)
    )
  }
}

module ATM {
  import ATMEmbeddings

  private int getNumberOfSinkSemSearchResults() { result = 100000000 }

  private predicate sinkSemSearchResults(
    EmbeddingLabel searchLabel, EmbeddingLabel resultLabel, float score
  ) =
    semanticSearch(sinkQueryEmbeddings/3, snapshotEmbeddings/3, getNumberOfSinkSemSearchResults/0)(searchLabel,
      resultLabel, score)

  /** `DataFlow::Configuration` for adaptive threat modeling (ATM). */
  class Configuration extends raw::TaintTracking::Configuration {
    Configuration() { this = "AdaptiveThreatModeling" }

    override predicate isSource(DataFlow::Node source) {
      // Is an existing source
      getCfg().isKnownSource(source)
    }

    override predicate isSource(DataFlow::Node source, DataFlow::FlowLabel lbl) {
      // Is an existing source
      getCfg().isKnownSource(source, lbl)
    }

    override predicate isSink(DataFlow::Node sink) {
      // Is in a result entity that is similar to a known sink-containing entity according to
      // semantic search
      exists(Entity resultEntity, EntityLabel resultLabel |
        sinkSemSearchResults(_, resultLabel, _) and
        sink = Mappers::getSinkCandidateWithinEntity(resultEntity) and
        resultLabel.getEntity() = resultEntity
      )
      or
      // Is an existing sink
      getCfg().isKnownSource(sink)
    }

    override predicate isSink(DataFlow::Node sink, DataFlow::FlowLabel lbl) {
      // Is in a result entity that is similar to a known sink-containing entity according to
      // semantic search
      exists(DataFlow::Node originalSink, EntityLabel seedLabel, EntityLabel resultLabel |
        getCfg().isKnownSink(originalSink, lbl) and
        seedLabel.getEntity() = Mappers::getEntityFromSink(sink) and
        sinkSemSearchResults(seedLabel, resultLabel, _) and
        sink = Mappers::getSinkCandidateWithinEntity(resultLabel.getEntity())
      )
      or
      // Is an existing sink
      getCfg().isKnownSink(sink, lbl)
    }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      getCfg().isSanitizer(node)
    }

    override predicate isSanitizerGuard(raw::TaintTracking::SanitizerGuardNode guard) {
      super.isSanitizerGuard(guard) or
      getCfg().isSanitizerGuard(guard)
    }

    override predicate isAdditionalFlowStep(
      DataFlow::Node src, DataFlow::Node trg, DataFlow::FlowLabel inlbl, DataFlow::FlowLabel outlbl
    ) {
      getCfg().isAdditionalFlowStep(src, trg, inlbl, outlbl)
    }
  }

  private Entity getSeedSinkEntity() {
    exists(DataFlow::Node sink |
      (getCfg().isKnownSink(sink) or getCfg().isKnownSink(sink, _)) and
      result = Mappers::getEntityFromSink(sink)
    )
  }

  private predicate sinkQueryEmbeddings(
    EmbeddingLabel label, int embeddingIndex, float embeddingValue
  ) {
    label.(EntityLabel).getEntity() = getSeedSinkEntity() and
    snapshotEmbeddings(label, embeddingIndex, embeddingValue)
  }

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * This module contains informational predicates about the results returned by adaptive threat
   * modeling (ATM).
   */
  module ResultsInfo {
    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * Holds if the node `source` is a source in the standard security query.
     */
    predicate isSourceASeed(DataFlow::Node source) {
      getCfg().isKnownSource(source) or getCfg().isKnownSource(source, _)
    }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * Holds if the node `sink` is a sink in the standard security query.
     */
    predicate isSinkASeed(DataFlow::Node sink) {
      getCfg().isKnownSink(sink) or getCfg().isKnownSink(sink, _)
    }

    private float scoreForSink(DataFlow::Node sink) {
      if isSinkASeed(sink)
      then result = 1.0
      else
        result =
          max(float score |
            exists(ATMEmbeddings::EntityLabel entityLabel |
              sinkSemSearchResults(_, entityLabel, score) and
              sink = Mappers::getSinkCandidateWithinEntity(entityLabel.getEntity())
            )
          )
    }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * Returns the score for the flow between the source `source` and the `sink` sink in the
     * boosted query.
     */
    float scoreForFlow(DataFlow::Node source, DataFlow::Node sink) { result = scoreForSink(sink) }

    /**
     * Pad a score returned from `scoreForFlow` to a particular length by adding a decimal point
     * if one does not already exist, and "0"s after that decimal point.
     *
     * Note that this predicate must itself define an upper bound on `length`, so that it has a
     * finite number of results. Currently this is defined as 12.
     */
    private string paddedScore(float score, int length) {
      // In this definition, we must restrict the values that `length` and `score` can take on so that the
      // predicate has a finite number of results.
      score = scoreForFlow(_, _) and
      length = result.length() and
      (
        // We need to make sure the padded score contains a "." so lexically sorting the padded scores is
        // equivalent to numerically sorting the scores.
        score.toString().charAt(_) = "." and
        result = score.toString()
        or
        not score.toString().charAt(_) = "." and
        result = score.toString() + "."
      )
      or
      result = paddedScore(score, length - 1) + "0" and
      length <= 12
    }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * Return a string representing the score of the flow between `source` and `sink` in the
     * boosted query.
     *
     * The returned string is a fixed length, such that lexically sorting the strings returned by
     * this predicate gives the same sort order as numerically sorting the scores of the flows.
     */
    string scoreStringForFlow(DataFlow::Node source, DataFlow::Node sink) {
      exists(float score |
        score = scoreForFlow(source, sink) and
        (
          // A length of 12 is equivalent to 10 decimal places.
          score.toString().length() >= 12 and
          result = score.toString().substring(0, 12)
          or
          score.toString().length() < 12 and
          result = paddedScore(score, 12)
        )
      )
    }

    private ATMEmbeddings::EmbeddingLabel bestSearchLabelsForSink(DataFlow::Node sink) {
      exists(ATMEmbeddings::EntityLabel resultLabel |
        sinkSemSearchResults(result, resultLabel, scoreForSink(sink)) and
        sink = Mappers::getSinkCandidateWithinEntity(resultLabel.getEntity())
      )
    }

    private newtype TSourceOrSinkOrigins =
      TOrigins(boolean isSnapshotSeed, boolean isSnapshotNonSeed) {
        (isSnapshotSeed = true or isSnapshotSeed = false) and
        (isSnapshotNonSeed = true or isSnapshotNonSeed = false)
      }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * A class representing the origins of a predicted source/sink.
     */
    class SourceOrSinkOrigins extends TSourceOrSinkOrigins {
      /**
       * EXPERIMENTAL. This API may change in the future.
       *
       * Whether the source/sink is a known source/sink in the snapshot.
       */
      boolean isSnapshotSeed;
      /**
       * EXPERIMENTAL. This API may change in the future.
       *
       * Whether the source/sink is a predicted source/sink that is near to a known source/sink in
       * the snapshot.
       */
      boolean isSnapshotNonSeed;

      SourceOrSinkOrigins() { this = TOrigins(isSnapshotSeed, isSnapshotNonSeed) }

      /**
       * EXPERIMENTAL. This API may change in the future.
       *
       * A string listing the origins of a predicted source/sink.
       *
       * Origins include:
       *
       * - `ql`: The source/sink is a known source/sink in the snapshot.
       * - `sim_snapshot`: The source/sink is a predicted source/sink that is near to a known
       * source/sink in the snapshot.
       */
      string listOfOriginComponents() {
        // Ensure that this predicate has exactly one result.
        result =
          "[" + any(string x | if isSnapshotSeed = true then x = "ql," else x = "") +
            any(string x | if isSnapshotNonSeed = true then x = "sim_snapshot," else x = "")
      }

      string toString() { result = "SourceOrSinkOrigin(" + listOfOriginComponents() + ")" }
    }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * The highest-scoring origins of the source.
     */
    SourceOrSinkOrigins originForSource(DataFlow::Node source) {
      result =
        TOrigins(any(boolean b | if isSourceASeed(source) then b = true else b = false), false)
    }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * The highest-scoring origins of the sink.
     */
    SourceOrSinkOrigins originForSink(DataFlow::Node sink) {
      result =
        TOrigins(any(boolean b | if isSinkASeed(sink) then b = true else b = false),
          any(boolean b |
            if exists(ATMEmbeddings::EntityLabel label | label = bestSearchLabelsForSink(sink))
            then b = true
            else b = false
          ))
    }

    /**
     * EXPERIMENTAL. This API may change in the future.
     *
     * Indicates whether the flow from source to sink is likely to be reported by the base security
     * query.
     *
     * Currently this is a heuristic: it ignores potential differences in the definitions of
     * additional flow steps.
     */
    predicate isFlowLikelyInBaseQuery(DataFlow::Node source, DataFlow::Node sink) {
      isSourceASeed(source) and isSinkASeed(sink)
    }
  }

  // To debug the ATM module, import this module by adding "import ATM::Debugging" to the top-level.
  module Debugging {
    query predicate sinkSemSearchResultsDebug = sinkSemSearchResults/3;

    query predicate atmSources(DataFlow::Node source) {
      any(ATM::Configuration cfg).isSource(source)
    }

    query predicate atmSinks(DataFlow::Node sink) { any(ATM::Configuration cfg).isSink(sink) }
  }
}
