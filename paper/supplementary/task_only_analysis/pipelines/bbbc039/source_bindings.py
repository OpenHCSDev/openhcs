# Derived OpenHCS source-binding declaration

from openhcs.constants.constants import AllComponents
from openhcs.core.source.source_bindings import (
    ComponentSelector,
    ImportedMetadataJoin,
    ImportedMetadataTable,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceSelector,
)
from openhcs.core.source.source_metadata import (
    MetadataExtractionRule,
    MetadataSource,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
)

source_bindings_config = SourceBindingsConfig(
    metadata_rules=(
        MetadataExtractionRule(
            source=MetadataSource.FILE_NAME,
            pattern='^(?:plate-(?P<plate>[^_]+)_)?well-(?P<well>[A-P]\\d{2})_site-(?P<site>[^_]+)_channel-(?P<channel>[^.]+)\\.(?:tif|tiff|bmp|png)$'
        ),
    ),
    source_filters=(
        SourceFilterClause(
            subject=SourceFilterSubject.FILE,
            match_type=SourceFilterMatchType.IS_IMAGE
        ),
    ),
    bindings=(
        NamedSourceBinding(
            alias='dna',
            selector=SourceSelector(
                metadata=(
                    MetadataSelector(
                        field='channel',
                        value='DNA'
                    ),
                )
            ),
            origin=SourceBindingOrigin.PIPELINE_START,
            component_identity=(
                ComponentSelector(
                    component=AllComponents.CHANNEL,
                    value='DNA'
                ),
            )
        ),
    ),
    imported_metadata_tables=(
        ImportedMetadataTable(
            location='source_manifest.csv',
            joins=(
                ImportedMetadataJoin(
                    image_metadata_field='well',
                    imported_metadata_field='well'
                ),
                ImportedMetadataJoin(
                    image_metadata_field='site',
                    imported_metadata_field='site'
                ),
                ImportedMetadataJoin(
                    image_metadata_field='channel',
                    imported_metadata_field='channel'
                )
            )
        ),
    ),
    grouping_metadata_fields=(
        'plate',
        'well'
    )
)