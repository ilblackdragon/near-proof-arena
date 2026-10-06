-- contracts v1.7 (additive): proven coverage of a run on a coverage-tiered
-- challenge (docs/CONTRACTS.md §11). NULL for every other challenge.
ALTER TABLE runs ADD COLUMN coverage jsonb;
