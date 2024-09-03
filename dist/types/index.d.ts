import * as React from 'react';

interface Images {
  [key: number]: string;
}

interface Theme {
  background: string,
  outlineColor: string,
  textColor: string,
  buttonColor: string,
  modalColor: string
}

interface Crop {
  unit: string,
  x?: number,
  y?: number,
  width?: number,
  height?: number
}

interface CropConfig {
  aspect?: number,
  crop?: Crop,
  maxWidth: number,
  minWidth: number,
  ruleOfThirds: boolean
}

interface MultiImageInputProps {
  images: Images;
  max?: number;
  setImages: (images: Images) => void;
  allowCrop?: boolean;
  cropConfig?: CropConfig;
  handleError?: (error: Error) => void;
  theme?: Theme;
}

declare const MultiImageInput: React.FC<MultiImageInputProps>;

export { MultiImageInput };
